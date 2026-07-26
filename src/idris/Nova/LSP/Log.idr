module Nova.LSP.Log

import System.File
import System

import Language.LSP.Severity

import Nova.LSP.Ref
import Nova.LSP.Configuration

%default total

||| Just the topics this server actually logs about — trimmed down
||| from the Idris2-LSP topics `nova-lsp` (the predecessor of this
||| module) inherited wholesale, most of which name Idris-specific
||| features (case splitting, clause generation, ...) Nova has none of.
public export
data Topic = Server | Channel | Diagnostic

export
Show Topic where
  show Server     = "Server"
  show Channel    = "Communication.Channel"
  show Diagnostic = "Notification.Diagnostic"

||| Logs a string with the provided severity level.
export
log : Ref LSPConf LSPConfiguration => Severity -> Topic -> String -> IO ()
log severity topic msg = do
  logHandle <- gets LSPConf logHandle
  Right () <- fPutStrLn logHandle "LOG \{show severity}:\{show topic}: \{msg}"
    | Left err => die "Error in fPutStrLn while writing to the log file: \{show err}"
  fflush logHandle

export
logD : Ref LSPConf LSPConfiguration => Topic -> String -> IO ()
logD = log Debug

export
logI : Ref LSPConf LSPConfiguration => Topic -> String -> IO ()
logI = log Info

export
logW : Ref LSPConf LSPConfiguration => Topic -> String -> IO ()
logW = log Warning

export
logE : Ref LSPConf LSPConfiguration => Topic -> String -> IO ()
logE = log Error

export
logC : Ref LSPConf LSPConfiguration => Topic -> String -> IO ()
logC = log Critical
