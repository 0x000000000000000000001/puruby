module Puruby.CodeGen where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Data.Tuple (Tuple(..))
import Data.Newtype (unwrap)
import PureScript.Backend.Optimizer.Syntax (BackendSyntax(..), Level(..), Pair(..), BackendOperator(..), BackendOperator1(..), BackendOperator2(..), BackendAccessor(..), BackendOperatorOrd(..), BackendOperatorNum(..))
import PureScript.Backend.Optimizer.Codegen.Tco (TcoExpr(..), tcoAnalysisOf)
import PureScript.Backend.Optimizer.Codegen.Tco as Tco
import Data.Array.NonEmpty as NEA
import PureScript.Backend.Optimizer.CoreFn (Ident(..), ProperName(..), Literal(..), ModuleName(..), Qualified(..), Prop(..))
import PureScript.Backend.Optimizer.Convert (BackendModule)
import Puruby.RubyAst (RubyExpr(..), RubyFile)
import Data.String as String
import Data.String.CodeUnits as CodeUnits

localId :: Maybe Ident -> Level -> String
localId mbI (Level lvl) =
  case mbI of
    Just (Ident n) -> 
      let
        n1 = String.replaceAll (String.Pattern "'") (String.Replacement "_") n
        n2 = String.replaceAll (String.Pattern "$") (String.Replacement "") n1
      in n2 <> "_" <> show lvl
    Nothing -> "v_" <> show lvl

type LoopCtx = { ident :: String, params :: Array String }

extractUncurriedAbs :: TcoExpr -> Maybe { args :: Array String, body :: TcoExpr }
extractUncurriedAbs (TcoExpr _ syntax) = case syntax of
  Abs args body ->
    let
      thisArgs = map (\(Tuple mbI lvl) -> localId mbI lvl) (Array.fromFoldable args)
    in case extractUncurriedAbs body of
      Just inner -> Just { args: thisArgs <> inner.args, body: inner.body }
      Nothing -> Just { args: thisArgs, body }
  UncurriedAbs args body ->
    Just { args: map (\(Tuple mbI lvl) -> localId mbI lvl) args, body }
  Typed _ inner -> extractUncurriedAbs inner
  _ -> Nothing

isSelfCall :: String -> TcoExpr -> Boolean
isSelfCall ident (TcoExpr _ syn) = case syn of
  Local (Just (Ident name)) _ -> sanitizeName name == ident
  _ -> false

translateExpr :: String -> Array LoopCtx -> Boolean -> TcoExpr -> RubyExpr
translateExpr modName loopCtx isTail (TcoExpr tcoAnalysis syntax) = case syntax of
  Lit lit -> case lit of
    LitString s -> RubyString s
    LitInt i -> RubyRaw (show i)
    LitNumber n -> RubyRaw (show n)
    LitBoolean b -> RubyRaw (if b then "true" else "false")
    LitChar c -> RubyString (CodeUnits.singleton c)
    LitArray arr -> RubyArray (map (translateExpr modName loopCtx false) arr)
    LitRecord props -> RubyHash (map (\(Prop k v) -> Tuple k (translateExpr modName loopCtx false v)) props)
  App fn args ->
    let
      flattenApp :: TcoExpr -> { fn :: TcoExpr, args :: Array TcoExpr }
      flattenApp e@(TcoExpr _ syn) = case syn of
        App f a -> let res = flattenApp f in { fn: res.fn, args: res.args <> Array.fromFoldable a }
        _ -> { fn: e, args: [] }
      
      flat = flattenApp (TcoExpr tcoAnalysis syntax)
      
      isTcoCall = case flat.fn of
        TcoExpr _ (Var (Qualified _ (Ident fnName))) ->
          let checkName = String.replaceAll (String.Pattern "'") (String.Replacement "_") (String.replaceAll (String.Pattern "$") (String.Replacement "") fnName)
          in isTail && Array.elem checkName (map _.ident loopCtx)
        TcoExpr _ (Local (Just (Ident fnName)) (Level lvl)) ->
          isTail && Array.elem (localId (Just (Ident fnName)) (Level lvl)) (map _.ident loopCtx)
        _ -> false
    in
      if isTcoCall then
        let
          targetCtx = case flat.fn of
             TcoExpr _ (Var (Qualified _ (Ident fnName))) ->
               let checkName = String.replaceAll (String.Pattern "'") (String.Replacement "_") (String.replaceAll (String.Pattern "$") (String.Replacement "") fnName)
               in Array.find (\c -> c.ident == checkName) loopCtx
             TcoExpr _ (Local (Just (Ident fnName)) (Level lvl)) ->
               Array.find (\c -> c.ident == localId (Just (Ident fnName)) (Level lvl)) loopCtx
             _ -> Nothing
        in case targetCtx of
          Just ctx ->
            RubyContinue ctx.ident (map (\arg -> translateExpr modName loopCtx false arg) flat.args)
          Nothing ->
            foldl (\acc arg -> RubyCall acc [(translateExpr modName loopCtx false arg)]) (translateExpr modName loopCtx false fn) (Array.fromFoldable args)
      else
        foldl (\acc arg -> RubyCall acc [(translateExpr modName loopCtx false arg)]) (translateExpr modName loopCtx false fn) (Array.fromFoldable args)
  UncurriedApp fn args ->
    RubyCall (translateExpr modName loopCtx false fn) (map (translateExpr modName loopCtx false) args)
  UncurriedEffectApp fn args ->
    RubyCall (translateExpr modName loopCtx false fn) (map (translateExpr modName loopCtx false) args)
  UncurriedAbs args body ->
    RubyUncurriedAbs (map (\(Tuple mbI _) -> case mbI of
      Just (Ident name) -> sanitizeName name
      Nothing -> "__unused") args) (translateExpr modName loopCtx false body)
  UncurriedEffectAbs args body ->
    RubyUncurriedAbs (map (\(Tuple mbI _) -> case mbI of
      Just (Ident name) -> sanitizeName name
      Nothing -> "__unused") args) (translateExpr modName loopCtx false body)
  Accessor expr acc -> case acc of
    GetProp prop ->
      RubyAccessor (translateExpr modName loopCtx false expr) prop
    GetIndex idx ->
      RubyIndexAccess (translateExpr modName loopCtx false expr) idx
    GetCtorField _ _ _ _ _ idx ->
      RubyIndexAccess (translateExpr modName loopCtx false expr) (idx + 1)
    _ -> RubyRaw "nil # TODO: Accessor"
  Update expr updates ->
    RubyRaw "nil"
  PrimOp op -> case op of
    Op1 op1 e -> translateOperator1 modName op1 (translateExpr modName loopCtx false e)
    Op2 op2 e1 e2 -> translateOperator2 modName op2 (translateExpr modName loopCtx false e1) (translateExpr modName loopCtx false e2)
  Var qi -> case qi of
    Qualified mbMod (Ident name) ->
      let
        qModName = case mbMod of
          Just (ModuleName m) -> Just (String.replaceAll (String.Pattern ".") (String.Replacement "_") m)
          Nothing -> Nothing
      in RubyGlobalVar qModName (sanitizeName name)
  PrimUndefined -> RubyRaw "nil"
  App fn args ->
    let
      flat = flattenApp (TcoExpr tcoAnalysis syntax)
      flattenApp :: TcoExpr -> { fn :: TcoExpr, args :: Array TcoExpr }
      flattenApp e@(TcoExpr _ syn) = case syn of
        App f a -> let res = flattenApp f in { fn: res.fn, args: res.args <> Array.fromFoldable a }
        _ -> { fn: e, args: [] }
    in
      if isTail then
        let targetCtx = Array.find (\ctx -> isSelfCall ctx.ident flat.fn) loopCtx
        in case targetCtx of
          Just ctx -> RubyContinue ctx.ident (map (\arg -> translateExpr modName loopCtx false arg) flat.args)
          Nothing -> foldl (\acc arg -> RubyCall acc [(translateExpr modName loopCtx false arg)]) (translateExpr modName loopCtx false flat.fn) flat.args
      else
        foldl (\acc arg -> RubyCall acc [(translateExpr modName loopCtx false arg)]) (translateExpr modName loopCtx false flat.fn) flat.args
  Abs args body ->
    foldr (\(Tuple mbI lvl) acc -> RubyAbs [localId mbI lvl] acc) (translateExpr modName loopCtx isTail body) (Array.fromFoldable args)
  Let mbI lvl val body ->
    RubyLet (localId mbI lvl) (translateExpr modName loopCtx false val) (translateExpr modName loopCtx isTail body)
  LetRec _ binds body ->
    let
      tcoInfo = unwrap tcoAnalysis
      isLoop = tcoInfo.role.isLoop
    in
      if isLoop && Array.length (Array.fromFoldable binds) == 1 then
        case Array.head (Array.fromFoldable binds) of
          Just (Tuple (Ident name) val) ->
            let
              javaName = sanitizeName name
            in case extractUncurriedAbs val of
              Just abs ->
                let
                  newCtx = { ident: javaName, params: abs.args }
                  loopBody = translateExpr modName (Array.snoc loopCtx newCtx) true abs.body
                in
                  RubyWhileTrue abs.args loopBody
              Nothing -> RubyLetRec [] (RubyRaw "\"TODO: LetRec\"")
          Nothing -> RubyLetRec [] (RubyRaw "\"TODO: LetRec\"")
      else
        RubyLetRec [] (RubyRaw "\"TODO: LetRec\"")
  Branch conds def ->
    let
      foldBranch :: Pair TcoExpr -> RubyExpr -> RubyExpr
      foldBranch (Pair c res) acc =
        RubyTernary (translateExpr modName loopCtx false c) (translateExpr modName loopCtx isTail res) acc
    in
      Array.foldr foldBranch (translateExpr modName loopCtx isTail def) (Array.fromFoldable conds)
  Local mbIdent (Level lvl) ->
    let
      varName = localId mbIdent (Level lvl)
      isLoopVar = Array.any (\ctx -> Array.elem varName ctx.params) loopCtx
    in
      RubyLocal (if isLoopVar then "__tco_" <> varName else varName)
  EffectBind _ _ _ _ -> RubyRaw "\"TODO: EffectBind\""
  EffectPure _ -> RubyRaw "\"TODO: EffectPure\""
  EffectDefer _ -> RubyRaw "\"TODO: EffectDefer\""
  Typed _ inner -> translateExpr modName loopCtx isTail inner
  CtorDef _ _ (Ident ctorName) fields ->
    let
      body = RubyArray (Array.cons (RubyString ctorName) (map (\arg -> RubyLocal arg) fields))
    in
      foldr (\arg acc -> RubyAbs [arg] acc) body fields
  CtorSaturated _ _ _ (Ident ctorName) args ->
    RubyArray (Array.cons (RubyString ctorName) (map (\(Tuple _ val) -> translateExpr modName loopCtx false val) (Array.fromFoldable args)))
  Fail msg -> RubyCall (RubyRaw "raise") [RubyString msg]
  _ -> RubyRaw ("\"TODO: " <> syntaxTag syntax <> "\"")

syntaxTag :: BackendSyntax TcoExpr -> String
syntaxTag = case _ of
  Var _ -> "Var"
  Local _ _ -> "Local"
  Lit _ -> "Lit"
  App _ _ -> "App"
  Abs _ _ -> "Abs"
  UncurriedApp _ _ -> "UncurriedApp"
  UncurriedAbs _ _ -> "UncurriedAbs"
  UncurriedEffectApp _ _ -> "UncurriedEffectApp"
  UncurriedEffectAbs _ _ -> "UncurriedEffectAbs"
  Accessor _ _ -> "Accessor"
  Update _ _ -> "Update"
  CtorSaturated _ _ _ _ _ -> "CtorSaturated"
  CtorDef _ _ _ _ -> "CtorDef"
  LetRec _ _ _ -> "LetRec"
  Let _ _ _ _ -> "Let"
  EffectBind _ _ _ _ -> "EffectBind"
  EffectPure _ -> "EffectPure"
  EffectDefer _ -> "EffectDefer"
  Branch _ _ -> "Branch"
  PrimOp _ -> "PrimOp"
  PrimEffect _ -> "PrimEffect"
  PrimUndefined -> "PrimUndefined"
  Fail _ -> "Fail"
  Typed _ _ -> "Typed"

translate :: BackendModule -> RubyFile
translate mod =
  let
    -- We just find `main` and translate it. For now we only care about Baby Step 1 (the single `main` binding).
    Tuple _ tcoBindings = foldl
      (\(Tuple env acc) group ->
          let
            tcoBinds = map (\(Tuple k v) -> Tuple k (Tco.analyze env v)) group.bindings
          in
            Tuple env (Array.snoc acc { recursive: group.recursive, bindings: tcoBinds })
      )
      (Tuple [] [])
      mod.bindings

    modNameStr = case mod.name of
      ModuleName m -> String.replaceAll (String.Pattern ".") (String.Replacement "_") m

    mainDecls = Array.concatMap
      ( \group ->
          if group.recursive && Array.length group.bindings == 1 then
            case Array.head group.bindings of
              Just (Tuple (Ident name) expr) ->
                case extractUncurriedAbs expr of
                  Just abs ->
                    let
                      javaName = sanitizeName name
                      newCtx = { ident: javaName, params: abs.args }
                      loopBody = translateExpr modNameStr [newCtx] true abs.body
                      funcBody = RubyWhileTrue abs.args loopBody
                    in
                      [RubyAssign (modNameStr <> "_" <> javaName) (RubyAbs abs.args funcBody)]
                  Nothing ->
                    [RubyAssign (modNameStr <> "_" <> sanitizeName name) (translateExpr modNameStr [] false expr)]
              Nothing -> []
          else
            map
              ( \(Tuple (Ident name) expr) ->
                  RubyAssign (modNameStr <> "_" <> sanitizeName name) (translateExpr modNameStr [] false expr)
              )
              group.bindings
      )
      tcoBindings

    dataClasses = Array.concatMap (\decl ->
        map (\ctor ->
            let
              safeCtorName = String.replaceAll (String.Pattern "'") (String.Replacement "_prime_") ctor.name
              args = Array.mapWithIndex (\i _ -> "value" <> show i) ctor.fields
            in
              RubyRaw ""
        ) decl.constructors
      ) mod.dataDecls

    decls = dataClasses <> mainDecls
  in
    { decls }

translateOperator1 :: String -> BackendOperator1 -> RubyExpr -> RubyExpr
translateOperator1 modName op e = case op of
  OpIsTag (Qualified mbMod (Ident tag)) ->
    RubyBinOp "==" (RubyIndexAccess e 0) (RubyString tag)
  OpBooleanNot -> RubyBinOp "!" (RubyRaw "") e
  OpIntBitNot -> RubyBinOp "~" (RubyRaw "") e
  OpIntNegate -> RubyBinOp "-" (RubyRaw "") e
  OpNumberNegate -> RubyBinOp "-" (RubyRaw "") e
  OpArrayLength -> RubyPropertyAccess e "length"
  _ -> RubyRaw ("\"TODO: Op1\"")


translateOperator2 _ op e1 e2 = case op of
  OpArrayIndex -> RubyDynamicIndexAccess e1 e2
  OpBooleanAnd -> RubyBinOp "&&" e1 e2
  OpBooleanOr -> RubyBinOp "||" e1 e2
  OpStringAppend -> RubyBinOp "+" e1 e2
  OpBooleanOrd OpEq -> RubyBinOp "==" e1 e2
  OpBooleanOrd OpNotEq -> RubyBinOp "!=" e1 e2
  OpBooleanOrd OpLt -> RubyBinOp "<" e1 e2
  OpBooleanOrd OpLte -> RubyBinOp "<=" e1 e2
  OpBooleanOrd OpGt -> RubyBinOp ">" e1 e2
  OpBooleanOrd OpGte -> RubyBinOp ">=" e1 e2
  OpIntNum OpAdd -> RubyBinOp "+" e1 e2
  OpIntNum OpSubtract -> RubyBinOp "-" e1 e2
  OpIntNum OpMultiply -> RubyBinOp "*" e1 e2
  OpIntNum OpDivide -> RubyBinOp "/" e1 e2
  OpIntOrd OpEq -> RubyBinOp "==" e1 e2
  OpIntOrd OpNotEq -> RubyBinOp "!=" e1 e2
  OpIntOrd OpGt -> RubyBinOp ">" e1 e2
  OpIntOrd OpGte -> RubyBinOp ">=" e1 e2
  OpIntOrd OpLt -> RubyBinOp "<" e1 e2
  OpIntOrd OpLte -> RubyBinOp "<=" e1 e2
  OpNumberNum OpAdd -> RubyBinOp "+" e1 e2
  OpNumberNum OpSubtract -> RubyBinOp "-" e1 e2
  OpNumberNum OpMultiply -> RubyBinOp "*" e1 e2
  OpNumberNum OpDivide -> RubyBinOp "/" e1 e2
  OpNumberOrd OpEq -> RubyBinOp "==" e1 e2
  OpNumberOrd OpNotEq -> RubyBinOp "!=" e1 e2
  OpNumberOrd OpGt -> RubyBinOp ">" e1 e2
  OpNumberOrd OpGte -> RubyBinOp ">=" e1 e2
  OpNumberOrd OpLt -> RubyBinOp "<" e1 e2
  OpNumberOrd OpLte -> RubyBinOp "<=" e1 e2
  OpCharOrd OpEq -> RubyBinOp "==" e1 e2
  OpCharOrd OpNotEq -> RubyBinOp "!=" e1 e2
  OpCharOrd OpGt -> RubyBinOp ">" e1 e2
  OpCharOrd OpGte -> RubyBinOp ">=" e1 e2
  OpCharOrd OpLt -> RubyBinOp "<" e1 e2
  OpCharOrd OpLte -> RubyBinOp "<=" e1 e2
  OpStringOrd OpEq -> RubyBinOp "==" e1 e2
  OpStringOrd OpNotEq -> RubyBinOp "!=" e1 e2
  OpStringOrd OpGt -> RubyBinOp ">" e1 e2
  OpStringOrd OpGte -> RubyBinOp ">=" e1 e2
  OpStringOrd OpLt -> RubyBinOp "<" e1 e2
  OpStringOrd OpLte -> RubyBinOp "<=" e1 e2
  _ -> RubyRaw "\"TODO: Op2\""

sanitizeName :: String -> String
sanitizeName n =
  let
    n' = String.replaceAll (String.Pattern "$") (String.Replacement "") (String.replaceAll (String.Pattern "'") (String.Replacement "_") n)
    isKeyword x = x == "void" || x == "class" || x == "return" || x == "const" || x == "new" || x == "throw" || x == "catch" || x == "try" || x == "if" || x == "else" || x == "while" || x == "for" || x == "do" || x == "switch" || x == "case" || x == "default" || x == "break" || x == "continue" || x == "boolean" || x == "byte" || x == "char" || x == "short" || x == "int" || x == "long" || x == "float" || x == "double" || x == "true" || x == "false" || x == "null" || x == "this" || x == "super" || x == "instanceof" || x == "public" || x == "protected" || x == "private" || x == "static" || x == "final" || x == "abstract" || x == "interface" || x == "implements" || x == "extends" || x == "package" || x == "import" || x == "throws" || x == "enum" || x == "assert" || x == "strictfp" || x == "native" || x == "synchronized" || x == "transient" || x == "volatile"
  in
    if isKeyword n' then "_" <> n' else n'
