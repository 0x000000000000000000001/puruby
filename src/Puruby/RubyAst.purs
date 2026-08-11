module Puruby.RubyAst where

import Prelude
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)

data RubyExpr
  = RubyString String
  | RubyCall RubyExpr (Array RubyExpr)
  | RubyFunction RubyExpr
  | RubyLetRec (Array (Tuple String RubyExpr)) RubyExpr
  | RubyWhileTrue (Array String) RubyExpr
  | RubyContinue String (Array RubyExpr)
  | RubyGlobalVar (Maybe String) String
  | RubyLocal String
  | RubyLet String RubyExpr RubyExpr
  | RubyBlock (Array RubyExpr)
  | RubyAccessor RubyExpr String
  | RubyPropertyAccess RubyExpr String
  | RubyIndexAccess RubyExpr Int
  | RubyDynamicIndexAccess RubyExpr RubyExpr
  | RubyIndexAssign RubyExpr RubyExpr RubyExpr
  | RubyTernary RubyExpr RubyExpr RubyExpr
  | RubyThunk RubyExpr
  | RubyAbs (Array String) RubyExpr
  | RubyUncurriedAbs (Array String) RubyExpr
  | RubyHash (Array (Tuple String RubyExpr))
  | RubyArray (Array RubyExpr)
  | RubyBinOp String RubyExpr RubyExpr
  | RubyRaw String
  | RubyAssign String RubyExpr

type RubyFile =
  { decls :: Array RubyExpr
  }
