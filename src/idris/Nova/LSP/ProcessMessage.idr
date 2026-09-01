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
import System.Clock
import System.File

import Nova.Kernel.Parser
import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Elaboration.Loader
import Nova.Eliminate

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
||| Clear diagnostics this root previously published to OTHER files'
||| URIs (see LSPConfiguration.crossDiags), so nothing goes stale
||| across reloads.
clearCrossDiags : Ref LSPConf LSPConfiguration => DocumentURI -> IO ()
clearCrossDiags root = do
  extras <- gets LSPConf (fromMaybe [] . lookup root . crossDiags)
  traverse_ (\u => sendDiagnostics u Nothing []) extras
  update LSPConf { crossDiags $= filter ((/= root) . fst) }

||| True iff the document's `DocState` was actually refreshed. On a
||| failed load (parse error, unreadable file, ...) the PREVIOUS
||| DocState stays — its tokens describe the OLD content, so callers
||| must not prompt the client to re-pull them against the new text.
loadURI : Ref LSPConf LSPConfiguration => DocumentURI -> Maybe Int -> IO Bool
loadURI uri version = do
  logI Server "Loading \{show uri}"
  t0 <- clockTime Monotonic
  let fpath = uri.path
  clearCrossDiags uri
  Right units <- loadProgram fpath
    | Left err => do
        logE Server "Failed to load \{show uri}: \{err.lmsg}"
        -- the open document's own text, for positioning a parse error
        -- at its span (UTF-16 column conversion needs the lines)
        src <- readFile fpath
        sendDiagnostics uri version
          [loadErrorDiagnostic (either (const "") id src) fpath err]
        -- a parse error in an IMPORTED file also lands in that file's
        -- own buffer, at its exact span — the open document only gets
        -- the whole-document banner naming it
        case (err.lfile, err.lrange) of
          (Just f, Just r) =>
            if f /= fpath
              then do
                Right depSrc <- readFile f
                  | Left _ => pure False
                let depUri = pathToURI f
                sendDiagnostics depUri Nothing
                  [mkParseDiagnostic (toLspRange (lines depSrc) r) err.lmsg]
                update LSPConf { crossDiags $= ((uri, [depUri]) ::) }
                pure False
              else pure False
          _ => pure False
  let Just root = last' units
    | Nothing => do logE Server "loadProgram returned no modules for \{show uri}"
                    pure False
  Right source <- readFile fpath
    | Left err => do logE Server "Cannot re-read \{fpath}: \{show err}"
                     pure False
  let report = elabProgramReport units
  let index = buildIndex fpath units
  -- the language is strict, so the report and index are BUILT by
  -- the lets above — this brackets the real work (parse + load +
  -- elaborate + report), which is what the user waits for on save
  t1 <- clockTime Monotonic
  let dt = timeDifference t1 t0
  let ms = seconds dt * 1000 + nanoseconds dt `div` 1000000
  setDoc uri (MkDocState source root index report version)
  sendDiagnostics uri version (toDiagnostics source root.mfix report)
  -- AFTER the diagnostics, so clients render the state before its
  -- timing (and the test client's read order stays deterministic)
  sendCustomNotification "nova/elabTime" (JObject
    [ ("uri", toJSON uri)
    , ("millis", JNumber (cast ms))
    , ("modules", JNumber (cast (length units)))
    ])
  pure True

-- ===== guards =====

||| Ask the client to drop its semantic-token caches and re-pull
||| (`workspace/semanticTokens/refresh`). Tokens are a client-pull
||| feature — the server cannot push them — and this request is the
||| only server-side lever, so it is gated on the client capability
||| that advertises support for it. A client without it re-pulls on
||| its own schedule and simply lags until the next edit.
semanticTokensRefresh : Ref LSPConf LSPConfiguration => IO ()
semanticTokensRefresh = do
  Just conf <- gets LSPConf initialized
    | Nothing => pure ()
  let supported = fromMaybe False $
        conf.capabilities.workspace >>= semanticTokens >>= refreshSupport
  when supported $
    sendRequestMessage WorkspaceSemanticTokensRefresh Nothing

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

-- ===== in-place elimination =====
--
-- One action per variable of the hole's context that HAS an
-- elimination (docs/NovaElaboration.txt, In-place elimination), each
-- carrying only what resolve needs to recompute it. The EDIT is not
-- computed here: every candidate is verified by re-elaborating the
-- file it would land in, and doing that per offer would cost one
-- elaboration per variable. Resolve pays it once, for the one picked.

||| What an offered action carries across the resolve round trip. The
||| hole travels by its Σ NAME, not by position: the buffer may have
||| moved under us between the offer and the pick, and a stale
||| position would silently address a different hole, where a stale
||| name simply is not found.
actionData : DocumentURI -> (holeName, var : String) -> (deep : Bool) -> JSON
actionData uri holeName var deep = JObject
  [ ("uri", toJSON uri)
  , ("hole", JString holeName)
  , ("var", JString var)
  , ("deep", JBoolean deep)
  ]

readActionData : JSON -> Maybe (DocumentURI, String, String, Bool)
readActionData (JObject fs) = do
  uri  <- lookup "uri" fs >>= fromJSON
  hole <- lookup "hole" fs >>= asString
  var  <- lookup "var" fs >>= asString
  let deep = case lookup "deep" fs of
               Just (JBoolean b) => b
               _ => False
  pure (uri, hole, var, deep)
 where
  asString : JSON -> Maybe String
  asString (JString x) = Just x
  asString _ = Nothing
readActionData _ = Nothing

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
  -- binder occurrences: ascribe the elaborated type
  case [ (r, txt) | (r, txt) <- doc.report.binderTable, posInRange pos r ] of
    ((r, txt) :: _) => do
      let content = MkMarkupContent Markdown ("```nova\n" ++ txt ++ "\n```")
      pure (pure (make (MkHover (make content) (Just (toLspRange lns r)))))
    [] => pure (pure (make MkNull))
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

handleRequest TextDocumentCodeAction params = whenActiveRequest $ \_ => do
  logI Channel "Received codeAction request for \{show params.textDocument.uri}"
  let none = the (List (OneOf [Command, CodeAction])) []
  Just doc <- getDoc params.textDocument.uri
    | Nothing => pure (pure (make none))
  let lns = lines doc.source
  let pos = fromLspPosition lns params.range.start
  -- the hole the cursor is IN; a range covering several holes is not
  -- a request to eliminate in all of them
  let Right v = holeAt doc.report pos.line pos.column
    | Left _ => pure (pure (make none))
  let taken = siblingLabels doc.report.holes v.hvDecl
  let acts = concatMap (action params.textDocument.uri v.hvDecl) (offers taken doc.report.qiits v)
  pure (pure (make (the (List (OneOf [Command, CodeAction])) (map make acts))))
 where
  action : DocumentURI -> DeclView -> (String, String, Bool) -> List CodeAction
  action u h (var, ty, hasDeep) =
    let one = MkCodeAction
                { title       = "eliminate \{var} : \{ty}"
                , kind        = Just RefactorRewrite
                , diagnostics = Nothing
                , isPreferred = Nothing
                , disabled    = Nothing
                , edit        = Nothing
                , command     = Nothing
                , data_       = Just (actionData u h.dvname var False)
                }
    in one :: (if hasDeep
                 then [ { title := "eliminate \{var} : \{ty} (fully)"
                        , data_ := Just (actionData u h.dvname var True) } one ]
                 else [])

handleRequest CodeActionResolve params = whenActiveRequest $ \_ => do
  logI Channel "Received codeAction/resolve request"
  let Just d = params.data_
    | Nothing => pure (Left (invalidParams "code action carries no data to resolve"))
  let Just (uri, holeName, var, deep) = readActionData d
    | Nothing => pure (Left (invalidParams "unrecognised code action data"))
  Just doc <- getDoc uri
    | Nothing => pure (Left (invalidParams "\{show uri} is not open"))
  let Just v = holeNamed doc.report holeName
    | Nothing => pure (Left (invalidRequest "the hole this action was offered at is gone — save and try again"))
  let opts = { optDeep := deep } defaultOptions
  Right (rng, txt) <- eliminateEdit uri.path doc.source v (siblingLabels doc.report.holes v.hvDecl) doc.report.qiits var opts
    | Left err => do
        logW Server "eliminate \{var} at \{holeName}: \{err}"
        pure (Left (invalidRequest err))
  let edit = MkTextEdit (toLspRange (lines doc.source) rng) txt
  -- STAMPED with the version the content was loaded at: this server
  -- reloads from disk and ignores didChange, so it cannot itself know
  -- the buffer has moved on — the client checks the stamp and refuses
  let tde = MkTextDocumentEdit
              (MkOptionalVersionedTextDocumentIdentifier uri doc.version)
              [make edit]
  pure (pure ({ edit := Just (MkWorkspaceEdit Nothing (Just [make tde]) Nothing) } params))

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
  ignore $ loadURI params.textDocument.uri (Just params.textDocument.version)

handleNotification TextDocumentDidSave params = whenActiveNotification $ \_ => do
  logI Channel "Received didSave notification for \{show params.textDocument.uri}"
  refreshed <- loadURI params.textDocument.uri Nothing
  -- semantic tokens are CLIENT-pull, and clients re-pull on buffer
  -- edits — but our tokens only change here, on the post-save reload
  -- (didChange is ignored), so by the time we have fresh tokens the
  -- client has stopped asking. Nudge it to invalidate and re-pull —
  -- but ONLY when the reload succeeded: after a failed reload the
  -- cached tokens still describe the PREVIOUS content, and forcing
  -- the client to re-apply them against the new text misplaces every
  -- highlight. Left alone, the client's own marks track the edit.
  when refreshed semanticTokensRefresh

handleNotification TextDocumentDidClose params = whenActiveNotification $ \_ => do
  logI Channel "Received didClose notification for \{show params.textDocument.uri}"
  clearDoc params.textDocument.uri

handleNotification method params = whenActiveNotification $ \_ =>
  logW Channel "Received unhandled notification for method \{stringify (toJSON method)}"
