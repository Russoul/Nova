module Nova.Docs.Render

-- Batch static-HTML renderer for .nova surface files: runs the same
-- loading pipeline the `nova elab` CLI runs (Nova.Elaboration.
-- Loader.loadProgram), reuses the LSP's own token classification
-- (Nova.LSP.SemanticTokens), and paints the source
-- with one <span class="tok-..."> per classified token — so a
-- rendered page's highlighting always matches what an editor's LSP
-- client shows, with no separate classifier to keep in sync.
--
-- GO-TO-DEFINITION, statically: the same name resolution the LSP's
-- definition request uses (Nova.LSP.Definitions — purely syntactic,
-- built from the loaded ModUnits) turns every resolvable
-- identifier/operator token into a link. Each rendered line carries
-- an id ("L<n>", 1-based), so a link's target is the defining item's
-- first line — same page as "#L37", cross-module as "nat.html#L12".
-- A written name that resolves to nothing but names a loaded module
-- links to that module's page (import heads navigate). Local
-- (λ/Π-bound) names resolve to nothing and stay plain — with the
-- LSP's own caveat that a local SHADOWING a global will link to the
-- global; resolution is best-effort syntactic, exactly like the
-- editor's.

import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Data.SnocList

import System
import System.File

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import Data.SortedMap

import Nova.Kernel.Parser
import Nova.Elaboration
import Nova.Elaboration.Loader
import Nova.LSP.Capabilities
import Nova.LSP.SemanticTokens
import Nova.LSP.Definitions

%default covering

-- ===== rendering =====

htmlEscape : String -> String
htmlEscape = concatMap esc . unpack
  where
    esc : Char -> String
    esc '&' = "&amp;"
    esc '<' = "&lt;"
    esc '>' = "&gt;"
    esc c   = singleton c

nth : Nat -> List a -> Maybe a
nth _        []        = Nothing
nth Z        (x :: _)  = Just x
nth (S k)    (_ :: xs) = nth k xs

||| `overlay`'s classified index, resolved back to a CSS class name via
||| the same legend the LSP advertises (Nova.LSP.Capabilities.
||| tokenTypeNames) — one source of truth for both.
classFor : Int -> String
classFor i = fromMaybe "plain" (nth (integerToNat (cast i)) tokenTypeNames)

||| Render one source line against the (start-ordered) tokens whose
||| span begins on it, returning the line's HTML and the tokens left
||| over for later lines. `pos` is the codepoint column already
||| emitted on this line. A token carrying an href renders as a link
||| instead of a span, same class either way.
renderLine : (lineNo : Int) -> (pos : Int) -> List Char -> List (Range, Int, Maybe String)
           -> (String, List (Range, Int, Maybe String))
renderLine _ _ cs [] = (htmlEscape (pack cs), [])
renderLine lineNo pos cs (tok :: rest) =
  let (MkRange (MkPosition sl sc) (MkPosition _ ec), kind, mhref) = tok in
  if sl /= lineNo
    then (htmlEscape (pack cs), tok :: rest)
    else
      let (gapChars, afterGap) = splitAt (integerToNat (cast (sc - pos))) cs
          (tokChars, afterTok) = splitAt (integerToNat (cast (ec - sc))) afterGap
          gapHtml = htmlEscape (pack gapChars)
          inner = htmlEscape (pack tokChars)
          tokHtml = case mhref of
                      Just href =>
                        "<a class=\"tok-" ++ classFor kind ++ "\" href=\"" ++ href ++ "\">" ++ inner ++ "</a>"
                      Nothing =>
                        "<span class=\"tok-" ++ classFor kind ++ "\">" ++ inner ++ "</span>"
          (restHtml, leftover) = renderLine lineNo ec afterTok rest
      in (gapHtml ++ tokHtml ++ restHtml, leftover)

||| Each line is wrapped in <span id="L<n>"> (1-based), the anchor
||| granularity links target.
renderLines : (lineNo : Int) -> List String -> List (Range, Int, Maybe String) -> List String
renderLines _ [] _ = []
renderLines lineNo (l :: ls) toks =
  let (html, leftover) = renderLine lineNo 0 (unpack l) toks
  in ("<span id=\"L" ++ show (lineNo + 1) ++ "\">" ++ html ++ "</span>")
       :: renderLines (lineNo + 1) ls leftover

||| Same classification a `semanticTokens/full` response carries
||| (Nova.LSP.SemanticTokens.getSemanticTokens), just emitted as HTML
||| spans instead of the LSP wire format's delta-encoded ints —
||| plus a per-token href from the resolver.
renderSource : String -> List (Range, TokenKind) -> (Range -> TokenKind -> Maybe String) -> String
renderSource source rawToks hrefOf =
  let sorted = sortTokens (map (\(r, k) => (r, tokenKindIndex k, hrefOf r k)) rawToks)
  in joinBy "\n" (renderLines 0 (lines source) sorted)

htmlPage : (title : String) -> String -> String
htmlPage title body = joinBy "\n"
  [ "<!DOCTYPE html>"
  , "<html>"
  , "<head>"
  , "<meta charset=\"utf-8\">"
  , "<title>" ++ htmlEscape title ++ "</title>"
  , "<link rel=\"stylesheet\" href=\"nova-docs.css\">"
  , "</head>"
  , "<body>"
  , "<h1>" ++ htmlEscape title ++ "</h1>"
  , "<pre><code class=\"nova-source\">"
  ++ body ++
  "</code></pre>"
  , "</body>"
  , "</html>"
  ]

-- ===== driver =====

baseNameOf : String -> String
baseNameOf path =
  let name = List1.last (split (== '/') path) in
  if isSuffixOf ".nova" name
    then pack (reverse (drop 5 (reverse (unpack name))))
    else name

||| The static go-to-definition resolver for one page: written name →
||| qualified (the module's own aliases, Nova.LSP.Definitions), then
||| the program-wide index gives (file, item range) → an href to the
||| defining line; a miss that names a loaded module links to its
||| page instead (import heads).
hrefResolver : (path : String) -> (lns : List String)
            -> SortedMap String String
            -> SortedMap String (String, NRange)
            -> SortedMap String ()
            -> Range -> TokenKind -> Maybe String
hrefResolver path lns aliases index pages r k =
  if not (isNameKind k) then Nothing else
  let txt = sliceRange lns r in
  if txt == "" then Nothing else
  let q = fromMaybe txt (SortedMap.lookup txt aliases) in
  case SortedMap.lookup q index of
    Just (file, MkRange (MkPosition dl _) _) =>
      let frag = "#L" ++ show (dl + 1) in
      Just (if file == path then frag else baseNameOf file ++ ".html" ++ frag)
    Nothing =>
      case SortedMap.lookup txt pages of
        Just () => Just (txt ++ ".html")
        Nothing => Nothing

||| Load and render one .nova file to a
||| standalone HTML page. Errors (parse/load failure) are reported,
||| not thrown — one bad file shouldn't abort the whole batch.
renderFile : String -> IO (Either String (String, String))
renderFile path = do
  Right units <- loadProgram path
    | Left err => pure (Left err.lmsg)
  let Just root = last' units
    | Nothing => pure (Left "loadProgram returned no modules for \{path}")
  Right source <- readFile path
    | Left err => pure (Left "cannot read \{path}: \{show err}")
  let lns = lines source
  let aliases = SortedMap.fromList (localAliases root)
  let index = SortedMap.fromList
                (map (\(n, f, rng) => (n, (f, rng))) (buildIndex path units))
  let pages = SortedMap.fromList
                (mapMaybe (\u => if u.mname == "" then Nothing
                                  else Just (u.mname, ())) units)
  let body = renderSource source (toList root.mtokens)
               (hrefResolver path lns aliases index pages)
  let base = baseNameOf path
  pure (Right (base, htmlPage base body))

indexPage : List String -> String
indexPage bases = joinBy "\n" $
  [ "<!DOCTYPE html>"
  , "<html>"
  , "<head>"
  , "<meta charset=\"utf-8\">"
  , "<title>Nova sources</title>"
  , "<link rel=\"stylesheet\" href=\"nova-docs.css\">"
  , "</head>"
  , "<body>"
  , "<h1>Nova sources</h1>"
  , "<ul>"
  ] ++ map (\b => "<li><a href=\"" ++ b ++ ".html\">" ++ htmlEscape b ++ "</a></li>") bases ++
  [ "</ul>"
  , "</body>"
  , "</html>"
  ]

processFile : (outDir : String) -> String -> IO (Maybe String)
processFile outDir path = do
  Right (base, html) <- renderFile path
    | Left err => do putStrLn "Error in \{path}: \{err}"; pure Nothing
  Right () <- writeFile (outDir ++ "/" ++ base ++ ".html") html
    | Left err => do putStrLn "Cannot write output for \{path}: \{show err}"; pure Nothing
  putStrLn "Rendered \{path} -> \{outDir}/\{base}.html"
  pure (Just base)

usage : String
usage = "Usage: nova-docs <output-dir> <file.nova> [<file.nova> ...]"

main : IO ()
main = do
  (_ :: outDir :: files@(_ :: _)) <- getArgs
    | _ => die usage
  bases <- traverse (processFile outDir) files
  let oks = catMaybes bases
  Right () <- writeFile (outDir ++ "/index.html") (indexPage oks)
    | Left err => do putStrLn "Cannot write index: \{show err}"; exitFailure
  when (length oks /= length files) exitFailure
