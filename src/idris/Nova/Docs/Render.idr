module Nova.Docs.Render

-- Batch static-HTML renderer for .nova surface files: runs the same
-- load/elaborate pipeline the `nova elab` CLI runs (Nova.Elaboration.
-- Loader.loadProgram), reuses the LSP's own token classification and
-- hole-state overlay (Nova.LSP.SemanticTokens), and paints the source
-- with one <span class="tok-..."> per classified token — so a
-- rendered page's highlighting always matches what an editor's LSP
-- client shows, with no separate classifier to keep in sync.

import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Data.SnocList

import System
import System.File

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import Nova.Kernel.Parser
import Nova.Elaboration
import Nova.Elaboration.Loader
import Nova.LSP.Capabilities
import Nova.LSP.SemanticTokens

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
||| emitted on this line.
renderLine : (lineNo : Int) -> (pos : Int) -> List Char -> List (Range, Int)
           -> (String, List (Range, Int))
renderLine _ _ cs [] = (htmlEscape (pack cs), [])
renderLine lineNo pos cs (tok :: rest) =
  let (MkRange (MkPosition sl sc) (MkPosition _ ec), kind) = tok in
  if sl /= lineNo
    then (htmlEscape (pack cs), tok :: rest)
    else
      let (gapChars, afterGap) = splitAt (integerToNat (cast (sc - pos))) cs
          (tokChars, afterTok) = splitAt (integerToNat (cast (ec - sc))) afterGap
          gapHtml = htmlEscape (pack gapChars)
          tokHtml = "<span class=\"tok-" ++ classFor kind ++ "\">" ++ htmlEscape (pack tokChars) ++ "</span>"
          (restHtml, leftover) = renderLine lineNo ec afterTok rest
      in (gapHtml ++ tokHtml ++ restHtml, leftover)

renderLines : (lineNo : Int) -> List String -> List (Range, Int) -> List String
renderLines _ [] _ = []
renderLines lineNo (l :: ls) toks =
  let (html, leftover) = renderLine lineNo 0 (unpack l) toks
  in html :: renderLines (lineNo + 1) ls leftover

||| Same classification+hole-overlay a `semanticTokens/full` response
||| carries (Nova.LSP.SemanticTokens.getSemanticTokens), just emitted
||| as HTML spans instead of the LSP wire format's delta-encoded ints.
renderSource : String -> List (Range, TokenKind) -> List (Range, Bool) -> String
renderSource source rawToks holeOccs =
  let overlaid = sortTokens (map (overlay holeOccs) rawToks)
  in joinBy "\n" (renderLines 0 (lines source) overlaid)

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

||| Surface hole syntax only (`?x`/`_x`/`_`), recolored by solved
||| state — same restriction and same source (ElabReport.holeTable)
||| as Nova.LSP.ProcessMessage's TextDocumentSemanticTokensFull.
holeOccsOf : ElabReport -> List (Range, Bool)
holeOccsOf report =
  [ (r, isJust h.hiSolution)
  | h <- report.holeTable
  , isPrefixOf "?" h.hiName || isPrefixOf "_" h.hiName
  , r <- h.hiOccs
  ]

baseNameOf : String -> String
baseNameOf path =
  let name = List1.last (split (== '/') path) in
  if isSuffixOf ".nova" name
    then pack (reverse (drop 5 (reverse (unpack name))))
    else name

||| Load, elaborate (for hole state) and render one .nova file to a
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
  let report = elabProgramReport units
  let holeOccs = holeOccsOf report
  let body = renderSource source (toList root.mtokens) holeOccs
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
