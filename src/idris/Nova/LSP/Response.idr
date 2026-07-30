module Nova.LSP.Response

import Data.OneOf
import Data.String

import Language.JSON
import Language.LSP.Message
import Language.LSP.Severity
import Language.LSP.Utils

import Nova.LSP.Ref
import Nova.LSP.Configuration
import Nova.LSP.Log

import System.File

%default covering

header : Int -> String
header l = "Content-Length: " ++ show l ++ "\r\n\r\n"

export
methodNotFound : ResponseError
methodNotFound = MkResponseError MethodNotFound "Method not implemented yet" JNull

export
parseError : ResponseError
parseError = MkResponseError ParseError "Parse error" JNull

export
internalError : String -> ResponseError
internalError msg = MkResponseError InternalError msg JNull

export
invalidRequest : String -> ResponseError
invalidRequest msg = MkResponseError InvalidRequest msg JNull

export
invalidParams : String -> ResponseError
invalidParams msg = MkResponseError InvalidParams msg JNull

export
serverNotInitialized : ResponseError
serverNotInitialized = MkResponseError ServerNotInitialized "" JNull

writeResponse : Ref LSPConf LSPConfiguration => JSON -> IO ()
writeResponse msg = do
  let body = stringify msg
  let hdr = header (cast (length body))
  outputHandle <- gets LSPConf outputHandle
  Right () <- fPutStr outputHandle (hdr ++ body)
    | Left err => log Error Server "Can't write response in writeResponse, reason: \{show err}"
  fflush outputHandle

||| Sends a new notification from the server to the client.
export
sendNotificationMessage : Ref LSPConf LSPConfiguration
                       => (method : Method Server Notification)
                       -> (params : MessageParams method)
                       -> IO ()
sendNotificationMessage method params = do
  let msg = toJSON $ MkNotificationMessage method params
  writeResponse msg
  logI Channel "Sent notification message for method \{stringify (toJSON method)}"
  logD Channel "Notification sent: \{stringify msg}"

||| Sends a response message to a request received from the client.
export
sendResponseMessage : Ref LSPConf LSPConfiguration
                   => (method : Method Client Request)
                   -> ResponseMessage method
                   -> IO ()
sendResponseMessage method resp = do
  let msg = toJSON resp
  writeResponse msg
  logI Channel "Sent response message for method \{stringify (toJSON method)}"
  logD Channel "Response sent: \{stringify msg}"

||| Sends an error response to an unknown/malformed method.
export
sendUnknownResponseMessage : Ref LSPConf LSPConfiguration => ResponseError -> IO ()
sendUnknownResponseMessage err = do
  -- Initialize is an arbitrary choice here: the method is unknown so
  -- any ResponseMessage shape works, the wire content is the same.
  writeResponse (toJSON {a = ResponseMessage Initialize} (Failure (make MkNull) err))
  logI Channel "Sent response to unknown method"

||| Sends a `publishDiagnostics` notification for a source, given its
||| already-computed LSP `Diagnostic` list (see `Nova.LSP.Diagnostics`).
export
sendDiagnostics : Ref LSPConf LSPConfiguration
               => (uri : DocumentURI)
               -> (version : Maybe Int)
               -> (diagnostics : List Diagnostic)
               -> IO ()
sendDiagnostics uri version diagnostics = do
  let params = MkPublishDiagnosticsParams uri version diagnostics
  logI Diagnostic "Sending diagnostics for \{show uri}"
  sendNotificationMessage TextDocumentPublishDiagnostics params
