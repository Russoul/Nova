module Nova.LSP.Configuration

import System.File

import Language.LSP.Message.Initialize
import Language.LSP.Message.URI

import Me.Russoul.Text.Range

import Nova.Kernel.Parser
import Nova.Elaboration
import Nova.Elaboration.Surface

%default total

||| Label for the configuration reference.
public export
data LSPConf : Type where

||| Everything produced by loading+elaborating one open document: the
||| raw source (semantic tokens are encoded relative to its lines —
||| see `Nova.LSP.SemanticTokens`), the root module's effective fixity
||| table (obligation pretty-printing needs it for infix layout), the
||| classified token spans, and the range-aware elaboration report.
||| One `DocState` per currently-open document (see `LSPConfiguration.docs`)
||| — this server has no notion of a project-wide "workspace" beyond
||| what each open file's own import graph resolves.
public export
record DocState where
  constructor MkDocState
  source   : String
  fixTable : FixTable
  tokens   : List (Range, TokenKind)
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
    }
