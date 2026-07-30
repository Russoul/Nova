module Nova.LSP.ProcessMessage

import Data.List
import Data.SnocList
import Data.String

import Language.JSON
import Language.LSP.Message
import Language.LSP.Utils

import Me.Russoul.Text.Range
import Me.Russoul.Text.Position

import System
import System.File

import Nova.Kernel.Parser
import Nova.Elaboration
import Nova.Elaboration.Loader

import Nova.LSP.Ref
import Nova.LSP.Configuration
import Nova.LSP.Capabilities
import Nova.LSP.Diagnostics
import Nova.LSP.SemanticTokens
import Nova.LSP.Definitions
import Nova.LSP.Encoding
import Nova.LSP.Response
import Nova.LSP.Log

%default covering

-- ===== per-document state table =====

setDoc : Ref LSPConf LSPConfiguration => DocumentURI -> DocState -> IO ()
setDoc uri st = update LSPConf { docs $= ((uri, st) ::) . filter ((/= uri) . fst) }

getDoc : Ref LSPConf LSPConfiguration => DocumentURI -> IO (Maybe DocState)
getDoc uri = gets LSPConf (lookup uri . docs)

clearDoc : Ref LSPConf LSPConfiguration => DocumentURI -> IO ()
clearDoc uri = update LSPConf { docs $= filter ((/= uri) . fst) }

-- ===== loading =====

||| Elaborate the file at `uri`'s path — read fresh from disk, same as
||| `nova elab` (see `Nova.Elaboration.Loader.loadProgram`, which
||| resolves the file's own import graph automatically) — cache the
||| result as this document's `DocState`, and publish diagnostics.
||| `loadProgram`'s last unit is always the root (mname == ""), i.e.
||| the opened file itself; that unit's tokens/fixity table are what
||| this document's semantic tokens and obligation pretty-printing use.
loadURI : Ref LSPConf LSPConfiguration => DocumentURI -> Maybe Int -> IO ()
loadURI uri version = do
  logI Server "Loading \{show uri}"
  let fpath = uri.path
  Right units <- loadProgram fpath
    | Left err => do
        logE Server "Failed to load \{show uri}: \{err}"
        sendDiagnostics uri version [loadErrorDiagnostic err]
  let Just root = last' units
    | Nothing => logE Server "loadProgram returned no modules for \{show uri}"
  Right source <- readFile fpath
    | Left err => logE Server "Cannot re-read \{fpath}: \{show err}"
  let report = elabProgramReport units
  let index = buildIndex fpath units
  setDoc uri (MkDocState source root index report)
  sendDiagnostics uri version (toDiagnostics source root.mfix report)

-- ===== guards =====

whenInitializedRequest : Ref LSPConf LSPConfiguration => (InitializeParams -> IO (Either ResponseError a)) -> IO (Either ResponseError a)
whenInitializedRequest k =
  case !(gets LSPConf initialized) of
    Just conf => k conf
    Nothing => do
      logE Server "Cannot process requests before initialization"
      pure (Left serverNotInitialized)

whenNotShutdownRequest : Ref LSPConf LSPConfiguration => IO (Either ResponseError a) -> IO (Either ResponseError a)
whenNotShutdownRequest k =
  if !(gets LSPConf isShutdown)
    then do
      logE Server "Cannot process requests after shutdown"
      pure (Left (invalidRequest "Server has been shutdown"))
    else k

whenActiveRequest : Ref LSPConf LSPConfiguration => (InitializeParams -> IO (Either ResponseError a)) -> IO (Either ResponseError a)
whenActiveRequest = whenNotShutdownRequest . whenInitializedRequest

whenInitializedNotification : Ref LSPConf LSPConfiguration => (InitializeParams -> IO ()) -> IO ()
whenInitializedNotification k =
  case !(gets LSPConf initialized) of
    Just conf => k conf
    Nothing => do
      logE Server "Cannot process notification before initialization"
      sendUnknownResponseMessage serverNotInitialized

whenNotShutdownNotification : Ref LSPConf LSPConfiguration => IO () -> IO ()
whenNotShutdownNotification k =
  if !(gets LSPConf isShutdown)
    then do
      logE Server "Cannot process notifications after shutdown"
      sendUnknownResponseMessage (invalidRequest "Server has been shutdown")
    else k

whenActiveNotification : Ref LSPConf LSPConfiguration => (InitializeParams -> IO ()) -> IO ()
whenActiveNotification = whenNotShutdownNotification . whenInitializedNotification

-- ===== requests =====

export
handleRequest : Ref LSPConf LSPConfiguration
             => (method : Method Client Request)
             -> (params : MessageParams method)
             -> IO (Either ResponseError (ResponseResult method))

handleRequest Initialize params = do
  logI Channel "Received initialization request"
  update LSPConf {initialized := Just params}
  logI Server "Server initialized"
  pure (pure (MkInitializeResult serverCapabilities (Just serverInfo)))

handleRequest Shutdown params = do
  logI Channel "Received shutdown request"
  update LSPConf {isShutdown := True}
  logI Server "Server ready to be shutdown"
  pure (pure (the (Maybe Null) Nothing))

handleRequest TextDocumentSemanticTokensFull params = whenActiveRequest $ \_ => do
  logI Channel "Received semanticTokens/full request for \{show params.textDocument.uri}"
  Just doc <- getDoc params.textDocument.uri
    | Nothing => pure (pure (make MkNull))
  let toks = getSemanticTokens doc.source (toList doc.rootUnit.mtokens)
  pure (pure (make (MkSemanticTokens Nothing toks)))

handleRequest TextDocumentDocumentSymbol params = whenActiveRequest $ \_ => do
  logI Channel "Received documentSymbol request for \{show params.textDocument.uri}"
  Just doc <- getDoc params.textDocument.uri
    | Nothing => pure (pure (make (the (List DocumentSymbol) [])))
  let syms = documentSymbols (lines doc.source) doc.rootUnit.mitems
  pure (pure (make syms))

handleRequest TextDocumentHover params = whenActiveRequest $ \_ => do
  logI Channel "Received hover request for \{show params.textDocument.uri}"
  Just doc <- getDoc params.textDocument.uri
    | Nothing => pure (pure (make MkNull))
  let lns = lines doc.source
  let pos = fromLspPosition lns params.position
  -- a hole occurrence under the cursor answers with the hole's
  -- judgement: context and type while open, the solution once solved
  let hits = [ (hi, r) | hi <- doc.report.holeTable, r <- hi.hiOccs
             , posInRange pos r ]
  case hits of
    [] =>
      -- binder occurrences: ascribe the elaborated type
      case [ (r, txt) | (r, txt) <- doc.report.binderTable, posInRange pos r ] of
        ((r, txt) :: _) => do
          let content = MkMarkupContent Markdown ("```nova\n" ++ txt ++ "\n```")
          pure (pure (make (MkHover (make content) (Just (toLspRange lns r)))))
        [] => pure (pure (make MkNull))
    ((hi, r) :: _) => do
      let kind = the String $
                   if hi.hiSolvable
                     then maybe "unsolved hole" (const "solved hole") hi.hiSolution
                     else "rigid hole"
      let text = kind ++ " " ++ hi.hiName ++ "\n" ++ hi.hiText
      let content = MkMarkupContent Markdown ("```nova\n" ++ text ++ "\n```")
      pure (pure (make (MkHover (make content) (Just (toLspRange lns r)))))
 where
  posInRange : Me.Russoul.Text.Position.Position -> Me.Russoul.Text.Range.Range -> Bool
  posInRange p (MkRange s e) = s <= p && p <= e

handleRequest TextDocumentDefinition params = whenActiveRequest $ \_ => do
  logI Channel "Received definition request for \{show params.textDocument.uri}"
  Just doc <- getDoc params.textDocument.uri
    | Nothing => pure (pure (make MkNull))
  let lns = lines doc.source
  let pos = fromLspPosition lns params.position
  let Just name = findIdentifierAt lns (toList doc.rootUnit.mtokens) pos
    | Nothing => pure (pure (make MkNull))
  let Just (file, rng) = resolveReference doc.rootUnit doc.defIndex name
    | Nothing => pure (pure (make MkNull))
  Right targetSource <- readFile file
    | Left err => do
        logE Server "Cannot read definition target \{file}: \{show err}"
        pure (pure (make MkNull))
  let loc = MkLocation (pathToURI file) (toLspRange (lines targetSource) rng)
  pure (pure (make loc))

handleRequest method params = whenActiveRequest $ \_ => do
  logW Channel "Received unsupported \{show (toJSON method)} request"
  pure (Left methodNotFound)

-- ===== notifications =====

export
handleNotification : Ref LSPConf LSPConfiguration
                   => (method : Method Client Notification)
                   -> (params : MessageParams method)
                   -> IO ()

handleNotification Exit params = do
  logI Channel "Received exit notification"
  status <- if !(gets LSPConf isShutdown)
              then logI Server "Quitting the server..." >> pure ExitSuccess
              else logC Server "Quitting the server without a proper shutdown" >> pure (ExitFailure 1)
  exitWith status

handleNotification TextDocumentDidOpen params = whenActiveNotification $ \_ => do
  logI Channel "Received didOpen notification for \{show params.textDocument.uri}"
  loadURI params.textDocument.uri (Just params.textDocument.version)

handleNotification TextDocumentDidSave params = whenActiveNotification $ \_ => do
  logI Channel "Received didSave notification for \{show params.textDocument.uri}"
  loadURI params.textDocument.uri Nothing

handleNotification TextDocumentDidClose params = whenActiveNotification $ \_ => do
  logI Channel "Received didClose notification for \{show params.textDocument.uri}"
  clearDoc params.textDocument.uri

handleNotification method params = whenActiveNotification $ \_ =>
  logW Channel "Received unhandled notification for method \{stringify (toJSON method)}"
