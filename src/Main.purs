module Main where

import Prelude
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Node.FS.Aff as FS
import Node.Encoding (Encoding(..))
import PureScript.Backend.Optimizer.App (coreFnModulesFromOutput)
import PureScript.Backend.Optimizer.Builder (buildModules)
import PureScript.Backend.Optimizer.CoreFn (Module(..), Ident(..))
import PureScript.Backend.Optimizer.Semantics.Foreign (coreForeignSemantics)
import Data.Map as Map
import Data.Set as Set
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.String as String
import Puruby.CodeGen (translate)
import Puruby.Printer (printFile)

main :: Effect Unit
main = launchAff_ do
  modules <- coreFnModulesFromOutput "output"
  
  buildModules
    { directives: Map.empty
    , analyzeCustom: \_ _ -> Nothing
    , foreignSemantics: coreForeignSemantics
    , traceIdents: Set.empty
    , onPrepareModule: \_ m -> pure m
    , onSkipModule: \_ _ -> pure Nothing
    , onCodegenModule: \_ _ backendMod _ -> do
        let modNameStr = unwrap backendMod.name
        let rubyAst = translate backendMod
        let rubyCode = printFile rubyAst
        
        let safeModName = String.replaceAll (String.Pattern ".") (String.Replacement "_") modNameStr
        
        -- Emit FFI stubs
        let
          foreignIdents = Map.keys backendMod.foreign
          ffiStubs = String.joinWith "\n" (map (\(Ident name) -> "$" <> safeModName <> "_" <> String.replaceAll (String.Pattern "'") (String.Replacement "_") name <> " ||= FFI_STUB") (Array.fromFoldable foreignIdents))
        
        -- Generate the module file
        FS.writeTextFile UTF8 ("output/" <> safeModName <> ".rb") (ffiStubs <> "\n\n" <> rubyCode)
        
    }
    modules

  let
    requires = String.joinWith "" (map (\(Module m) -> "require_relative '" <> String.replaceAll (String.Pattern ".") (String.Replacement "_") (unwrap m.name) <> "'\n") (Array.fromFoldable modules))
    ffiStubHelper = "class FFIStubClass\n  def call(*args)\n    self\n  end\n  def [](*args)\n    self\n  end\nend\nFFI_STUB = FFIStubClass.new\n\n"
    ffis = """
$Effect_bindE = ->(a) { ->(f) { ->() { f.call(a.call()).call() } } }
$Effect_pureE = ->(a) { ->() { a } }
$Effect_Console_log = ->(s) { ->() { puts s } }
$Data_Semigroup_concatString = ->(a) { ->(b) { a + b } }
"""
  
  FS.writeTextFile UTF8 "output/main_run.rb" (ffiStubHelper <> ffis <> "\n" <> requires <> "\n$Main_main.call()\n")
