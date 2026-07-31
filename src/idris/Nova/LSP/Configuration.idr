module Nova.LSP.Configuration

import System.File

import Language.LSP.Message.Initialize
import Language.LSP.Message.URI

import Me.Russoul.Text.Range

import Nova.Elaboration

%default total

||| Label for the configuration reference.
public export
data LSPConf : Type where

||| Everything produced by loading+elaborating one open document: the
||| raw source, the ROOT module itself (its fixity table, items and
||| tokens are all read straight off it — see `Nova.LSP.SemanticTokens`
||| /`Nova.LSP.Definitions`), the range-aware elaboration report, and a
||| definition index spanning every module the root transitively
||| imports (`Nova.LSP.Definitions.buildIndex`), since go-to-definition
||| can jump into a file that isn't itself open. One `DocState` per
||| currently-open document (see `LSPConfiguration.docs`) — this server
||| has no notion of a project-wide "workspace" beyond what each open
||| file's own import graph resolves.
public export
record DocState where
  constructor MkDocState
  source   : String
  rootUnit : ModUnit
  defIndex : List (String, String, Range)
  report   : ElabReport

||| Type for the LSP server configuration.
public export
record LSPConfiguration where
  constructor MkLSPConfiguration
  ||| File handle where to read LSP messages.
  inputHandle : File
  ||| File handle where to output LSP messages.
  outputHandle : File
  ||| File handle where to put log messages.
  logHandle : File
  ||| Set once `initialize` succeeds.
  initialized : Maybe InitializeParams
  ||| True once the client has sent `shutdown`.
  isShutdown : Bool
  ||| Currently open documents and their last load's results.
  docs : List (DocumentURI, DocState)
  ||| URIs OTHER than the root that the root's last load published
  ||| diagnostics to (a parse error in an imported file lands in that
  ||| file's own buffer) — cleared before each reload so nothing goes
  ||| stale.
  crossDiags : List (DocumentURI, List DocumentURI)

||| Server default configuration. Uses standard input and standard
||| output for input/output.
export
defaultConfig : LSPConfiguration
defaultConfig =
  MkLSPConfiguration
    { inputHandle  = stdin
    , outputHandle = stdout
    , logHandle    = stderr
    , initialized  = Nothing
    , isShutdown   = False
    , docs         = []
    , crossDiags   = []
    }
