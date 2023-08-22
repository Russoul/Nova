module Nova.Test.Test

import Data.String
import Data.AVL
import Data.Location

import System.File.ReadWrite
import System.File
import System.Path
import System

import Text.Parser.CharUtil
import Text.Parser.Fork

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Substitution
import Nova.Core.Unification
import Nova.Core.Pretty

import Nova.Surface.Elaboration
import Nova.Surface.Language
import Nova.Surface.ModuleSystem
import Nova.Surface.Operator
import Nova.Surface.Parser
import Nova.Surface.ParserUtil
import Nova.Surface.SemanticToken

novaDirectory = "src/nova"
moduleDescriptionFile = novaDirectory </> "modules.npkg"

checkEverything : IO ()
checkEverything = Prelude.do
   Just modules <- readModuleDescription moduleDescriptionFile
     | Nothing => die "Can't read module description file: \{moduleDescriptionFile}"
   (sig, omega, ops, unifySt, modules) <- checkModules [<] empty [<] initialUnifySt empty novaDirectory modules
   pure ()

main : IO ()
main = checkEverything
