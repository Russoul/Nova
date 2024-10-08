module Nova.Test.Test

import Me.Russoul.Data.Location
import Me.Russoul.Text.Parser

import Data.String
import Data.AVL

import System.File.ReadWrite
import System.File
import System.Path
import System

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Pretty

import Nova.Surface.ModuleSystem
import Nova.Surface.Operator
import Nova.Surface.SemanticToken

novaDirectory = "src/nova"
moduleDescriptionFile = novaDirectory </> "modules.npkg"

checkEverything : IO ()
checkEverything = Prelude.do
   Just modules <- readModuleDescription moduleDescriptionFile
     | Nothing => die "Can't read module description file: \{moduleDescriptionFile}"
   Right (ops, sig, omega, nextOmegaIdx, namedHoles, modules) <- ModuleSystem.checkEverything [<] [<] empty 0 empty empty novaDirectory modules
     | Left (f, r, err) => die (renderDocTerm err)
   pure ()

main : IO ()
main = checkEverything
