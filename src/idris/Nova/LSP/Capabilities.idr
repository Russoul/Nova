module Nova.LSP.Capabilities

import Language.JSON
import Language.LSP.Message

import Nova.Kernel.Parser

%default total

syncOptions : TextDocumentSyncOptions
syncOptions = MkTextDocumentSyncOptions
  { openClose         = Just True
  -- we never act on didChange payloads (diagnostics/tokens only
  -- refresh on didOpen/didSave — see Nova.LSP.ProcessMessage), so
  -- there is nothing incremental sync would buy us
  , change            = Just TextDocumentSyncKind.None
  , willSave          = Nothing
  , willSaveWaitUntil = Nothing
  , save              = Just (make (MkSaveOptions (Just True)))
  }

||| Legend order fixes the integer each `TokenKind` encodes as on the
||| wire (see `Nova.LSP.SemanticTokens.encode`) — index must match
||| `tokenKindIndex`. Names are LSP's own standard semantic token
||| types, chosen to match what an editor's default theme already
||| colours sensibly without a Nova-specific theme.
tokenKinds : List TokenKind
tokenKinds = [Keyword, Identifier, Operator, Number, Comment]

export
tokenKindIndex : TokenKind -> Int
tokenKindIndex Keyword    = 0
tokenKindIndex Identifier = 1
tokenKindIndex Operator   = 2
tokenKindIndex Number     = 3
tokenKindIndex Comment    = 4

tokenKindName : TokenKind -> String
tokenKindName Keyword    = "keyword"
tokenKindName Identifier = "variable"
tokenKindName Operator   = "operator"
tokenKindName Number     = "number"
tokenKindName Comment    = "comment"

semanticTokensLegend : SemanticTokensLegend
semanticTokensLegend = MkSemanticTokensLegend (map tokenKindName tokenKinds) []

semanticTokensOptions : SemanticTokensOptions
semanticTokensOptions = MkSemanticTokensOptions
  semanticTokensLegend
  (Just (make False))
  (Just (make True))

||| Default server capabilities sent to clients during `initialize`.
||| Implemented (see `Nova.LSP.ProcessMessage`): textDocumentSync,
||| semanticTokensProvider, hoverProvider, definitionProvider,
||| documentSymbolProvider — plus inlayHintProvider, injected into the
||| initialize response by the raw-JSON path (the pinned lsp-lib's
||| record predates it). Everything else is explicitly disabled rather
||| than left `Nothing`, so a client never mistakes "we didn't say"
||| for "try it anyway".
export
serverCapabilities : ServerCapabilities
serverCapabilities =
  MkServerCapabilities
    { textDocumentSync                 = Just (make syncOptions)
    , completionProvider               = Nothing
    , hoverProvider                    = Just (make True)
    , signatureHelpProvider            = Nothing
    , definitionProvider               = Just (make True)
    , declarationProvider              = Just (make False)
    , typeDefinitionProvider           = Just (make False)
    , implementationProvider           = Just (make False)
    , referencesProvider               = Just (make False)
    , documentHighlightProvider        = Just (make False)
    , documentSymbolProvider           = Just (make True)
    , codeActionProvider               = Just (make False)
    , codeLensProvider                 = Nothing
    , documentLinkProvider             = Nothing
    , colorProvider                    = Just (make False)
    , documentFormattingProvider       = Just (make False)
    , documentRangeFormattingProvider  = Just (make False)
    , documentOnTypeFormattingProvider = Nothing
    , renameProvider                   = Just (make False)
    , foldingRangeProvider             = Just (make False)
    , executeCommandProvider           = Nothing
    , selectionRangeProvider           = Just (make False)
    , linkedEditingRangeProvider       = Just (make False)
    , callHierarchyProvider            = Just (make False)
    , semanticTokensProvider           = Just (make semanticTokensOptions)
    , monikerProvider                  = Just (make False)
    , workspaceSymbolProvider          = Just (make False)
    , workspace                        = Nothing
    , experimental                     = Nothing
    }

export
serverInfo : ServerInfo
serverInfo = MkServerInfo { name = "nova-lsp", version = Just "0.1" }
