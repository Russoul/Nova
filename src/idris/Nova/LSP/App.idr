module Nova.LSP.App

import Data.List1
import Data.String

import Language.JSON
import Language.LSP.Message
import Language.LSP.Utils

import Nova.LSP.Configuration
import Nova.LSP.Log
import Nova.LSP.ProcessMessage
import Nova.LSP.Ref
import Nova.LSP.Response

import System
import System.File

import Nova.Profile

data Header = ContentLength Int | ContentType String | StartContent

parseHeader : String -> Maybe Header
parseHeader "\r\n" = Just StartContent
parseHeader str =
  if "Content-Length:" `isPrefixOf` str
    then let (_ ::: xs) = split (== ':') str in
             ContentLength <$> parseInteger (fastConcat xs)
    else if "Content-Type:" `isPrefixOf` str
      then let (_ ::: xs) = split (== ':') str in
               Just (ContentType (fastConcat xs))
      else Nothing

parseHeaderPart : (h : File) -> IO (Either FileError (Maybe Int))
parseHeaderPart h = do
  Right line <- fGetHeader h
    | Left err => pure (Left err)
  case parseHeader line of
    Just (ContentLength l) => parseHeaderPart h *> pure (Right (Just l))
    Just (ContentType s) => parseHeaderPart h
    Just StartContent => pure (Right Nothing)
    Nothing => pure (Right Nothing)

handleMessage : Ref LSPConf LSPConfiguration => IO ()
handleMessage = do
  inputHandle <- gets LSPConf inputHandle
  Right (Just l) <- parseHeaderPart inputHandle
    | _ => do
        logD Channel "Cannot parse message header"
        sendUnknownResponseMessage parseError
  Right msg <- fGetChars inputHandle l
    | Left err => do
        logE Server "Cannot retrieve body of message: \{show err}"
        sendUnknownResponseMessage (internalError "Error while recovering the content part of a message")
  logD Channel "Received message: \{msg}"
  let Just msg = parse msg
    | _ => do
        logE Channel "Cannot parse message"
        sendUnknownResponseMessage parseError
  let JObject fields = msg
    | _ => do
        logE Channel "Message is not a JSON object"
        sendUnknownResponseMessage (invalidRequest "Message is not object")
  let Just (JString "2.0") = lookup "jsonrpc" fields
    | _ => do
        logE Channel "Message has no jsonrpc field"
        sendUnknownResponseMessage (invalidRequest "jsonrpc is not \"2.0\"")
  case lookup "method" fields of
    Just methodJSON => do
      case lookup "id" fields of
        Just idJSON => do -- request
          let Just id = fromJSON {a = OneOf [Int, String]} idJSON
            | _ => do
                logE Channel "Message id is not of the correct type"
                sendUnknownResponseMessage (invalidRequest "id is not int or string")
          let Just method = fromJSON {a = Method Client Request} methodJSON
            | _ => do
                logE Channel "Method not found"
                sendResponseMessage Initialize (Failure (extend id) methodNotFound)
          logI Channel "Received request for method \{show (toJSON method)}"
          let Just params = fromMaybeJSONParameters method (lookup "params" fields)
            | _ => do
                logE Channel "Message with method \{show (toJSON method)} has invalid parameters"
                sendResponseMessage method (Failure (extend id) (invalidParams "Invalid params for send \{show methodJSON}"))
          result <- handleRequest method params
          sendResponseMessage method $ case result of
            Left error => Failure (extend id) error
            Right result => Success (extend id) result

        Nothing => do -- notification
          let Just method = fromJSON {a = Method Client Notification} methodJSON
            | _ => do
                logE Channel "Method not found"
                sendUnknownResponseMessage methodNotFound
          logI Channel "Received notification for method \{show (toJSON method)}"
          let Just params = fromMaybeJSONParameters method (lookup "params" fields)
            | _ => do
                logE Channel "Message with method \{show (toJSON method)} has invalid parameters"
                sendUnknownResponseMessage (invalidParams "Invalid params for send \{show methodJSON}")
          handleNotification method params

    Nothing => do -- response to a server-initiated request — not tracked
      let Just idJSON = lookup "id" fields
        | _ => do
            logE Channel "Received message with neither method nor id"
            sendUnknownResponseMessage (invalidRequest "Message does not have method or id")
      logW Server "Ignoring response with id \{show idJSON}"

runServer : Ref LSPConf LSPConfiguration => IO ()
runServer = handleMessage >> runServer

main : IO ()
main = do
  -- the LSP always elaborates under STRICT CONVERSION: the editor is
  -- the migration/authoring surface, and its diagnostics must be the
  -- strict subset's obligations — no mode to configure
  setStrictConv True
  l <- newRef LSPConf defaultConfig
  runServer
