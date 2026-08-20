module Nova.LSP.TestClient

-- A black-box LSP integration-test client: spawns a `nova-lsp` binary
-- over a bidirectional pipe (`System.File.Process.popen2`), drives a
-- fixed scripted conversation (initialize -> didOpen -> read
-- diagnostics -> semanticTokens/full -> shutdown/exit), and prints a
-- normalized, deterministic report for golden diffing (see
-- `tests/nova-lsp/*`). Deliberately talks raw JSON-RPC (just
-- `Language.JSON`), not the server's own `lsp-lib` message types —
-- this is meant to catch wire-format bugs a shared type layer between
-- client and server could hide.

import Data.List
import Data.List1
import Data.Maybe
import Data.String

import Language.JSON
import Language.LSP.Utils

import System
import System.File

%default covering

-- ===== transport =====

writeMessage : File -> JSON -> IO ()
writeMessage h msg = do
  let body = stringify msg
  let hdr = "Content-Length: " ++ show (length body) ++ "\r\n\r\n"
  ignore $ fPutStr h (hdr ++ body)
  fflush h

data Header = ContentLength Int | ContentType String | StartContent

parseHeader : String -> Maybe Header
parseHeader "\r\n" = Just StartContent
parseHeader str =
  if "Content-Length:" `isPrefixOf` str
    then let (_ ::: xs) = split (== ':') str in ContentLength <$> parseInteger (fastConcat xs)
    else if "Content-Type:" `isPrefixOf` str
      then let (_ ::: xs) = split (== ':') str in Just (ContentType (fastConcat xs))
      else Nothing

-- Mirrors `Nova.LSP.App`'s own header-reading trick: the recursive
-- call consumes the remaining header lines (up to the blank line),
-- while the ContentLength branch's `pure` supplies the actual result.
readHeaderLen : File -> IO (Maybe Int)
readHeaderLen h = do
  Right line <- fGetHeader h
    | Left _ => pure Nothing
  case parseHeader line of
    Just (ContentLength l) => readHeaderLen h *> pure (Just l)
    Just (ContentType _) => readHeaderLen h
    Just StartContent => pure Nothing
    Nothing => pure Nothing

||| Contrib's JSON parser mangles surrogate-PAIR escapes: each \uXXXX
||| decodes alone, and a lone surrogate is not a character. The server
||| (lsp-lib) escapes EVERY wide character, so supplementary-plane
||| content arrives exclusively as pairs — decode those to literal
||| characters before parsing, leaving BMP escapes (which the parser
||| handles) untouched. An escaped backslash never fuses with a
||| following 'u'.
decodeSurrogatePairs : String -> String
decodeSurrogatePairs = pack . go . unpack
 where
  hexD : Char -> Maybe Int
  hexD c =
    if isDigit c then Just (ord c - ord '0')
    else if c >= 'a' && c <= 'f' then Just (10 + ord c - ord 'a')
    else if c >= 'A' && c <= 'F' then Just (10 + ord c - ord 'A')
    else Nothing

  hex4 : Char -> Char -> Char -> Char -> Maybe Int
  hex4 a b c d = do
    a' <- hexD a; b' <- hexD b; c' <- hexD c; d' <- hexD d
    pure (((a' * 16 + b') * 16 + c') * 16 + d')

  go : List Char -> List Char
  go ('\\' :: '\\' :: rest) = '\\' :: '\\' :: go rest
  go ('\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: i :: rest) =
    case (hex4 a b c d, hex4 e f g i) of
      (Just hi, Just lo) =>
        if hi >= 0xD800 && hi <= 0xDBFF && lo >= 0xDC00 && lo <= 0xDFFF
          then chr (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) :: go rest
          else '\\' :: 'u' :: go (a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: i :: rest)
      _ => '\\' :: 'u' :: go (a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: i :: rest)
  go (c :: rest) = c :: go rest
  go [] = []

readMessage : File -> IO (Maybe JSON)
readMessage h = do
  Just l <- readHeaderLen h
    | Nothing => pure Nothing
  Right body <- fGetChars h l
    | Left _ => pure Nothing
  pure (parse (decodeSurrogatePairs body))

dieMsg : String -> IO a
dieMsg msg = putStrLn ("ERROR: " ++ msg) >> exitWith (ExitFailure 1)

-- ===== JSON helpers =====

getField : String -> JSON -> Maybe JSON
getField k (JObject kvs) = lookup k kvs
getField _ _ = Nothing

getPath : List String -> JSON -> Maybe JSON
getPath [] j = Just j
getPath (k :: ks) j = getField k j >>= getPath ks

asArray : JSON -> Maybe (List JSON)
asArray (JArray xs) = Just xs
asArray _ = Nothing

asString : JSON -> Maybe String
asString (JString s) = Just s
asString _ = Nothing

asInt : JSON -> Maybe Int
asInt (JNumber d) = Just (cast d)
asInt _ = Nothing

req : Int -> String -> JSON -> JSON
req id method params = JObject [("jsonrpc", JString "2.0"), ("id", JNumber (cast id)), ("method", JString method), ("params", params)]

notif : String -> JSON -> JSON
notif method params = JObject [("jsonrpc", JString "2.0"), ("method", JString method), ("params", params)]

-- ===== decoding the semanticTokens/full response =====

nth : Nat -> List a -> Maybe a
nth _     []        = Nothing
nth Z     (x :: _)   = Just x
nth (S n) (_ :: xs)  = nth n xs

kindName : List String -> Int -> String
kindName legend kind = fromMaybe "?\{show kind}" (nth (cast kind) legend)

||| (line, startChar, length, kindName), decoded from LSP's relative
||| delta encoding.
-- ===== UTF-16 column conversion =====
-- LSP `character` offsets and semantic-token deltas are UTF-16 code
-- units; this client works in codepoints (unpack). Implemented
-- INDEPENDENTLY of the server's Nova.LSP.Encoding on purpose: sharing
-- the conversion would let a bug there cancel out here, and this
-- client exists to catch exactly that class of wire bug.

||| codepoint column -> UTF-16 units, within the given line
cpToU16 : String -> Int -> Int
cpToU16 line col = go (unpack line) col 0
 where
  go : List Char -> Int -> Int -> Int
  go [] _ acc = acc
  go (c :: cs) k acc =
    if k <= 0 then acc
    else go cs (k - 1) (acc + (if ord c > 0xFFFF then 2 else 1))

||| UTF-16 units -> codepoint column, within the given line
u16ToCp : String -> Int -> Int
u16ToCp line u = go (unpack line) u 0
 where
  go : List Char -> Int -> Int -> Int
  go [] _ acc = acc
  go (c :: cs) k acc =
    let w = if ord c > 0xFFFF then 2 else 1 in
    if k < w then acc else go cs (k - w) (acc + 1)

||| an LSP character offset -> codepoint column, via the line index;
||| a line we do not have (another file's range) stays raw
cpColAt : List String -> Int -> Int -> Int
cpColAt lns line ch = case drop (cast line) lns of
  (l :: _) => u16ToCp l ch
  [] => ch

decodeTokens : List String -> List Int -> List (Int, Int, Int, String)
decodeTokens legend = go 0 0
 where
  go : Int -> Int -> List Int -> List (Int, Int, Int, String)
  go line col xs =
    case xs of
      (dl :: dc :: len :: kind :: _ :: rest) =>
        let line' = line + dl
            col'  = if dl == 0 then col + dc else dc
        in (line', col', len, kindName legend kind) :: go line' col' rest
      _ => []

renderToken : (lns : List String) -> (Int, Int, Int, String) -> String
renderToken lns (line, col, len, kind) =
  let cs = cpColAt lns line col
      ce = cpColAt lns line (col + len)
  in "  L\{show (line + 1)}:\{show (cs + 1)}+\{show (ce - cs)} \{kind}"

renderDiagnostic : (lns : List String) -> JSON -> String
renderDiagnostic lns d =
  let range = fromMaybe "?" (do
                r <- getField "range" d
                sl <- getPath ["start", "line"] r >>= asInt
                sc <- getPath ["start", "character"] r >>= asInt
                el <- getPath ["end", "line"] r >>= asInt
                ec <- getPath ["end", "character"] r >>= asInt
                pure "L\{show (sl + 1)}:\{show (cpColAt lns sl sc + 1)}-L\{show (el + 1)}:\{show (cpColAt lns el ec + 1)}")
      sev = case getField "severity" d >>= asInt of
              Just 1 => "error"
              Just 2 => "warning"
              Just 3 => "info"
              Just 4 => "hint"
              _ => "?"
      msg = fromMaybe "?" (getField "message" d >>= asString)
  in "  [\{range}] (\{sev}) \{msg}"

renderRange : (lns : List String) -> JSON -> String
renderRange lns r =
  fromMaybe "?" (do
    sl <- getPath ["start", "line"] r >>= asInt
    sc <- getPath ["start", "character"] r >>= asInt
    el <- getPath ["end", "line"] r >>= asInt
    ec <- getPath ["end", "character"] r >>= asInt
    pure "L\{show (sl + 1)}:\{show (cpColAt lns sl sc + 1)}-L\{show (el + 1)}:\{show (cpColAt lns el ec + 1)}")

renderSymbol : (lns : List String) -> JSON -> String
renderSymbol lns s =
  let name = fromMaybe "?" (getField "name" s >>= asString)
      kind = fromMaybe (-1) (getField "kind" s >>= asInt)
      rng  = fromMaybe "?" (map (renderRange lns) (getField "range" s))
  in "  \{name} (kind \{show kind}) [\{rng}]"

-- ===== finding a search word's position, for the definition test =====

isPrefixOfChars : List Char -> List Char -> Bool
isPrefixOfChars [] _ = True
isPrefixOfChars (_ :: _) [] = False
isPrefixOfChars (x :: xs) (y :: ys) = x == y && isPrefixOfChars xs ys

findInLine : List Char -> List Char -> Maybe Int
findInLine word = go 0
 where
  go : Int -> List Char -> Maybe Int
  go _ [] = Nothing
  go i cs@(_ :: rest) = if isPrefixOfChars word cs then Just i else go (i + 1) rest

||| The (line, column) — both 0-based codepoint indices, matching what
||| the server itself works in before UTF-16 conversion — of the first
||| occurrence of `word` in `content`.
findWordPosition : String -> String -> Maybe (Int, Int)
findWordPosition word content = go 0 (lines content)
 where
  wordChars : List Char
  wordChars = unpack word
  go : Int -> List String -> Maybe (Int, Int)
  go _ [] = Nothing
  go lineNo (l :: ls) =
    case findInLine wordChars (unpack l) of
      Just col => Just (lineNo, col)
      Nothing  => go (lineNo + 1) ls

basename : String -> String
basename path = List1.last (split (== '/') path)

dirname : String -> String
dirname path =
  case reverse (forget (split (== '/') path)) of
    (_ :: parentRev@(_ :: _)) => joinBy "/" (reverse parentRev)
    _ => "."

||| Normalized go-to-definition result: whether the target is the SAME
||| file as the one we opened (a real absolute path would break golden
||| tests across checkouts, so it's never printed) or another file
||| (named by basename only), plus the target range.
renderDefinition : (lns : List String) -> String -> JSON -> String
renderDefinition lns fixtureUri JNull = "null"
renderDefinition lns fixtureUri result =
  fromMaybe "?" (do
    uri <- getField "uri" result >>= asString
    rng <- getField "range" result
    let label = if uri == fixtureUri then "SAME FILE" else "OTHER FILE: \{basename uri}"
    -- another file's content is not at hand, so its columns print raw
    let rlns = if uri == fixtureUri then lns else []
    pure "\{label} [\{renderRange rlns rng}]")

||| Normalized hover result: the markdown value flattened to one line
||| (newlines shown as ⏎) plus the answer range.
renderHover : (lns : List String) -> JSON -> String
renderHover lns JNull = "null"
renderHover lns result =
  fromMaybe "?" (do
    value <- getPath ["contents", "value"] result >>= asString
    let flat = fastConcat (map (\c => if c == '\n' then " ⏎ " else cast c) (unpack value))
    let rng = maybe "?" (renderRange lns) (getField "range" result)
    pure "[\{rng}] \{flat}")

||| Read until a NON-notification message arrives, rendering any
||| publishDiagnostics notifications passed on the way (cross-file
||| diagnostics arrive interleaved with response traffic).
readDraining : File -> (fixtureUri : String) -> (lns : List String) -> (normalise : String -> String) -> IO (Maybe JSON)
readDraining h fixtureUri lns normalise = do
  Just msg <- readMessage h
    | Nothing => pure Nothing
  case getField "method" msg of
    Just (JString "textDocument/publishDiagnostics") => do
      let uri = fromMaybe "?" (getPath ["params", "uri"] msg >>= asString)
      let label = if uri == fixtureUri then "FIXTURE" else basename uri
      let diags = fromMaybe [] (getPath ["params", "diagnostics"] msg >>= asArray)
      putStrLn "DIAGNOSTICS FOR \{label} (\{show (length diags)}):"
      traverse_ (putStrLn . normalise . renderDiagnostic (if uri == fixtureUri then lns else [])) diags
      readDraining h fixtureUri lns normalise
    -- the timing notification: nondeterministic value, so the golden
    -- pins only its presence and shape
    Just (JString "nova/elabTime") => do
      let ok = isJust (getPath ["params", "millis"] msg >>= asInt)
             && isJust (getPath ["params", "modules"] msg >>= asInt)
      putStrLn ("ELABTIME: " ++ (if ok then "reported" else "malformed"))
      readDraining h fixtureUri lns normalise
    _ => pure (Just msg)

||| Replace every occurrence of `needle` (non-empty) in `hay`.
replaceAll : (needle : String) -> (repl : String) -> String -> String
replaceAll needle repl hay = pack (go (unpack hay))
 where
  n : List Char
  n = unpack needle
  go : List Char -> List Char
  go [] = []
  go cs@(c :: rest) =
    if n /= [] && isPrefixOf n cs
      then unpack repl ++ go (drop (length n) cs)
      else c :: go rest

-- ===== the scripted conversation =====

||| `word`'s first occurrence in the fixture is used as the cursor
||| position for a `textDocument/definition` request — the caller
||| picks a word whose resolution (or deliberate non-resolution, e.g.
||| an unbound name) is worth pinning down in a golden test.
export
runLspTest : (lspBinPath : String) -> (fixtureAbsPath : String) -> (word : String) -> IO ()
runLspTest lspBinPath fixtureAbsPath word = do
  Right content <- readFile fixtureAbsPath
    | Left err => dieMsg "cannot read fixture \{fixtureAbsPath}: \{show err}"
  let lns = lines content
  Right proc <- popen2 lspBinPath
    | Left err => dieMsg "cannot spawn \{lspBinPath}: \{show err}"

  writeMessage proc.input (req 1 "initialize" (JObject
    [ ("processId", JNull), ("rootUri", JNull)
    -- advertise refresh support so the didSave step below can pin the
    -- server's workspace/semanticTokens/refresh nudge
    , ("capabilities", JObject
        [ ("workspace", JObject
            [ ("semanticTokens", JObject [("refreshSupport", JBoolean True)]) ])
        ])
    ]))
  Just initResp <- readMessage proc.output
    | Nothing => dieMsg "no response to initialize"
  let legend = fromMaybe [] (do
                 arr <- getPath ["result", "capabilities", "semanticTokensProvider", "legend", "tokenTypes"] initResp
                 xs <- asArray arr
                 traverse asString xs)
  putStrLn "LEGEND: \{show legend}"
  -- pin the advertised capabilities of every implemented method: a
  -- REAL client (unlike this one) refuses to send requests the server
  -- did not advertise, so a handler behind a false flag is dead code
  let cap = \k => stringify (fromMaybe JNull (getPath ["result", "capabilities", k] initResp))
  putStrLn "CAPS: hover=\{cap "hoverProvider"} definition=\{cap "definitionProvider"} documentSymbol=\{cap "documentSymbolProvider"}"

  writeMessage proc.input (notif "initialized" (JObject []))

  let uri = "file://" ++ fixtureAbsPath
  writeMessage proc.input (notif "textDocument/didOpen" (JObject
    [ ("textDocument", JObject
        [ ("uri", JString uri), ("languageId", JString "nova")
        , ("version", JNumber 1), ("text", JString content)
        ])
    ]))

  Just diagMsg <- readMessage proc.output
    | Nothing => dieMsg "no publishDiagnostics notification"
  let diags = fromMaybe [] (getPath ["params", "diagnostics"] diagMsg >>= asArray)
  putStrLn "DIAGNOSTICS (\{show (length diags)}):"
  -- absolute paths in messages (a parse error names its file) would
  -- break golden portability across checkouts
  let normalise = replaceAll fixtureAbsPath "FIXTURE" . replaceAll (dirname fixtureAbsPath) "DIR"
  traverse_ (putStrLn . normalise . renderDiagnostic lns) diags

  writeMessage proc.input (req 2 "textDocument/semanticTokens/full" (JObject [("textDocument", JObject [("uri", JString uri)])]))
  Just toksResp <- readDraining proc.output uri lns normalise
    | Nothing => dieMsg "no response to semanticTokens/full"
  let rawToks = fromMaybe [] (do
                  arr <- getPath ["result", "data"] toksResp
                  xs <- asArray arr
                  traverse asInt xs)
  let toks = decodeTokens legend rawToks
  putStrLn "TOKENS (\{show (length toks)}):"
  traverse_ (putStrLn . renderToken lns) toks

  writeMessage proc.input (req 3 "textDocument/documentSymbol" (JObject [("textDocument", JObject [("uri", JString uri)])]))
  Just symResp <- readDraining proc.output uri lns normalise
    | Nothing => dieMsg "no response to documentSymbol"
  let syms = fromMaybe [] (getPath ["result"] symResp >>= asArray)
  putStrLn "SYMBOLS (\{show (length syms)}):"
  traverse_ (putStrLn . renderSymbol lns) syms

  let Just (wline, wcol) = findWordPosition word content
    | Nothing => dieMsg "word '\{word}' not found in fixture"
  -- the cursor goes over the wire in UTF-16 units, like every LSP
  -- `character` — a fixture line with a supplementary-plane char
  -- (𝕌 is one) skews every later column otherwise
  let wch = case drop (cast wline) lns of
              (l :: _) => cpToU16 l wcol
              [] => wcol
  writeMessage proc.input (req 4 "textDocument/definition" (JObject
    [ ("textDocument", JObject [("uri", JString uri)])
    , ("position", JObject [("line", JNumber (cast wline)), ("character", JNumber (cast wch))])
    ]))
  Just defResp <- readDraining proc.output uri lns normalise
    | Nothing => dieMsg "no response to definition"
  let defResult = fromMaybe JNull (getField "result" defResp)
  putStrLn "DEFINITION(\{word}): \{renderDefinition lns uri defResult}"

  writeMessage proc.input (req 5 "textDocument/hover" (JObject
    [ ("textDocument", JObject [("uri", JString uri)])
    , ("position", JObject [("line", JNumber (cast wline)), ("character", JNumber (cast wch))])
    ]))
  Just hovResp <- readDraining proc.output uri lns normalise
    | Nothing => dieMsg "no response to hover"
  let hovResult = fromMaybe JNull (getField "result" hovResp)
  putStrLn "HOVER(\{word}): \{renderHover lns hovResult}"

  -- a save reloads the document (fresh diagnostics for it and any
  -- cross-file targets, drained here) and — when the reload SUCCEEDS
  -- — ends with the server asking the client to re-pull semantic
  -- tokens (tokens are client-pull, and the client's own re-pull
  -- triggers all fire BEFORE the reload that changes them). A FAILED
  -- reload must stay silent: the cached tokens describe the old
  -- content. The sentinel request bounds the wait either way — the
  -- server answers strictly in order, so whatever the didSave
  -- produced arrives before the sentinel's response.
  writeMessage proc.input (notif "textDocument/didSave" (JObject
    [ ("textDocument", JObject [("uri", JString uri)]) ]))
  writeMessage proc.input (req 7 "textDocument/documentSymbol" (JObject [("textDocument", JObject [("uri", JString uri)])]))
  Just afterSave <- readDraining proc.output uri lns normalise
    | Nothing => dieMsg "no message after didSave"
  case getField "method" afterSave >>= asString of
    Just m => do
      putStrLn "SERVER REQUEST AFTER DIDSAVE: \{m}"
      -- answer it, as a real client would (the server discards the
      -- reply), then consume the sentinel's response
      case getField "id" afterSave of
        Just idJ => writeMessage proc.input (JObject [("jsonrpc", JString "2.0"), ("id", idJ), ("result", JNull)])
        Nothing => pure ()
      ignore $ readDraining proc.output uri lns normalise
    Nothing => putStrLn "SERVER REQUEST AFTER DIDSAVE: none"

  writeMessage proc.input (req 6 "shutdown" JNull)
  Just _ <- readDraining proc.output uri lns normalise
    | Nothing => dieMsg "no response to shutdown"
  writeMessage proc.input (notif "exit" JNull)

  exitCode <- popen2Wait proc
  putStrLn "SERVER EXIT CODE: \{show exitCode}"
