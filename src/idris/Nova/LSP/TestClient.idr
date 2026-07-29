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

readMessage : File -> IO (Maybe JSON)
readMessage h = do
  Just l <- readHeaderLen h
    | Nothing => pure Nothing
  Right body <- fGetChars h l
    | Left _ => pure Nothing
  pure (parse body)

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

renderToken : (Int, Int, Int, String) -> String
renderToken (line, col, len, kind) =
  "  L\{show (line + 1)}:\{show (col + 1)}+\{show len} \{kind}"

renderDiagnostic : JSON -> String
renderDiagnostic d =
  let range = fromMaybe "?" (do
                r <- getField "range" d
                sl <- getPath ["start", "line"] r >>= asInt
                sc <- getPath ["start", "character"] r >>= asInt
                el <- getPath ["end", "line"] r >>= asInt
                ec <- getPath ["end", "character"] r >>= asInt
                pure "L\{show (sl + 1)}:\{show (sc + 1)}-L\{show (el + 1)}:\{show (ec + 1)}")
      msg = fromMaybe "?" (getField "message" d >>= asString)
  in "  [\{range}] \{msg}"

renderRange : JSON -> String
renderRange r =
  fromMaybe "?" (do
    sl <- getPath ["start", "line"] r >>= asInt
    sc <- getPath ["start", "character"] r >>= asInt
    el <- getPath ["end", "line"] r >>= asInt
    ec <- getPath ["end", "character"] r >>= asInt
    pure "L\{show (sl + 1)}:\{show (sc + 1)}-L\{show (el + 1)}:\{show (ec + 1)}")

renderSymbol : JSON -> String
renderSymbol s =
  let name = fromMaybe "?" (getField "name" s >>= asString)
      kind = fromMaybe (-1) (getField "kind" s >>= asInt)
      rng  = fromMaybe "?" (map renderRange (getField "range" s))
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

||| Normalized go-to-definition result: whether the target is the SAME
||| file as the one we opened (a real absolute path would break golden
||| tests across checkouts, so it's never printed) or another file
||| (named by basename only), plus the target range.
renderDefinition : String -> JSON -> String
renderDefinition fixtureUri JNull = "null"
renderDefinition fixtureUri result =
  fromMaybe "?" (do
    uri <- getField "uri" result >>= asString
    rng <- getField "range" result
    let label = if uri == fixtureUri then "SAME FILE" else "OTHER FILE: \{basename uri}"
    pure "\{label} [\{renderRange rng}]")

||| Normalized hover result: the markdown value flattened to one line
||| (newlines shown as ⏎) plus the answer range.
renderHover : JSON -> String
renderHover JNull = "null"
renderHover result =
  fromMaybe "?" (do
    value <- getPath ["contents", "value"] result >>= asString
    let flat = fastConcat (map (\c => if c == '\n' then " ⏎ " else cast c) (unpack value))
    let rng = maybe "?" renderRange (getField "range" result)
    pure "[\{rng}] \{flat}")

renderHint : JSON -> String
renderHint h =
  let pos = fromMaybe "?" (do
              l <- getPath ["position", "line"] h >>= asInt
              c <- getPath ["position", "character"] h >>= asInt
              pure "L\{show (l + 1)}:\{show (c + 1)}")
      label = fromMaybe "?" (getField "label" h >>= asString)
      kind = fromMaybe (-1) (getField "kind" h >>= asInt)
  in "  [\{pos}] (kind \{show kind})\{label}"

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
  Right proc <- popen2 lspBinPath
    | Left err => dieMsg "cannot spawn \{lspBinPath}: \{show err}"

  writeMessage proc.input (req 1 "initialize" (JObject [("processId", JNull), ("rootUri", JNull), ("capabilities", JObject [])]))
  Just initResp <- readMessage proc.output
    | Nothing => dieMsg "no response to initialize"
  let legend = fromMaybe [] (do
                 arr <- getPath ["result", "capabilities", "semanticTokensProvider", "legend", "tokenTypes"] initResp
                 xs <- asArray arr
                 traverse asString xs)
  putStrLn "LEGEND: \{show legend}"
  let inlay = fromMaybe JNull (getPath ["result", "capabilities", "inlayHintProvider"] initResp)
  putStrLn "INLAY PROVIDER: \{stringify inlay}"

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
  traverse_ (putStrLn . renderDiagnostic) diags

  writeMessage proc.input (req 2 "textDocument/semanticTokens/full" (JObject [("textDocument", JObject [("uri", JString uri)])]))
  Just toksResp <- readMessage proc.output
    | Nothing => dieMsg "no response to semanticTokens/full"
  let rawToks = fromMaybe [] (do
                  arr <- getPath ["result", "data"] toksResp
                  xs <- asArray arr
                  traverse asInt xs)
  let toks = decodeTokens legend rawToks
  putStrLn "TOKENS (\{show (length toks)}):"
  traverse_ (putStrLn . renderToken) toks

  writeMessage proc.input (req 3 "textDocument/documentSymbol" (JObject [("textDocument", JObject [("uri", JString uri)])]))
  Just symResp <- readMessage proc.output
    | Nothing => dieMsg "no response to documentSymbol"
  let syms = fromMaybe [] (getPath ["result"] symResp >>= asArray)
  putStrLn "SYMBOLS (\{show (length syms)}):"
  traverse_ (putStrLn . renderSymbol) syms

  let Just (wline, wcol) = findWordPosition word content
    | Nothing => dieMsg "word '\{word}' not found in fixture"
  writeMessage proc.input (req 4 "textDocument/definition" (JObject
    [ ("textDocument", JObject [("uri", JString uri)])
    , ("position", JObject [("line", JNumber (cast wline)), ("character", JNumber (cast wcol))])
    ]))
  Just defResp <- readMessage proc.output
    | Nothing => dieMsg "no response to definition"
  let defResult = fromMaybe JNull (getField "result" defResp)
  putStrLn "DEFINITION(\{word}): \{renderDefinition uri defResult}"

  writeMessage proc.input (req 5 "textDocument/hover" (JObject
    [ ("textDocument", JObject [("uri", JString uri)])
    , ("position", JObject [("line", JNumber (cast wline)), ("character", JNumber (cast wcol))])
    ]))
  Just hovResp <- readMessage proc.output
    | Nothing => dieMsg "no response to hover"
  let hovResult = fromMaybe JNull (getField "result" hovResp)
  putStrLn "HOVER(\{word}): \{renderHover hovResult}"

  writeMessage proc.input (req 6 "textDocument/inlayHint" (JObject
    [ ("textDocument", JObject [("uri", JString uri)])
    , ("range", JObject
        [ ("start", JObject [("line", JNumber 0), ("character", JNumber 0)])
        , ("end", JObject [("line", JNumber 9999), ("character", JNumber 0)])
        ])
    ]))
  Just hintResp <- readMessage proc.output
    | Nothing => dieMsg "no response to inlayHint"
  let hints = fromMaybe [] (getPath ["result"] hintResp >>= asArray)
  putStrLn "INLAY HINTS (\{show (length hints)}):"
  traverse_ (putStrLn . renderHint) hints

  writeMessage proc.input (req 7 "shutdown" JNull)
  Just _ <- readMessage proc.output
    | Nothing => dieMsg "no response to shutdown"
  writeMessage proc.input (notif "exit" JNull)

  exitCode <- popen2Wait proc
  putStrLn "SERVER EXIT CODE: \{show exitCode}"
