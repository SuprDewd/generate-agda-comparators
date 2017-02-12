module CompGen ( AgdaType(..)
               , makeEq
               , makeEqs

               , makeLt
               , makeLts

               , maybeParens

               , typeName
               , eqName
               , ltName
               ) where

import qualified Data.Map.Strict as Map
import Data.Char
import Data.List

type TypeName = String
type ConstructorName = String
type FunctionName = String

data AgdaType = Custom TypeName [(ConstructorName, [AgdaType])]
              | Builtin TypeName FunctionName FunctionName
              deriving (Show)

typeName :: AgdaType -> TypeName
typeName (Custom name _) = name
typeName (Builtin name _ _) = name

withDeps :: Map.Map TypeName AgdaType -> AgdaType -> Map.Map TypeName AgdaType
withDeps deps tp@(Builtin name _ _) = Map.insertWith const name tp deps
withDeps deps tp@(Custom name cons)
  | name `Map.member` deps = deps
  | otherwise              = foldl' withDeps (Map.insert name tp deps) (concatMap snd cons)

camelCase : TypeName -> String
camelCase s = toLower (head s) : filter (not . (`elem` "() ")) (tail s)

eqName :: AgdaType -> String
eqName (Builtin _ fun _) = fun
eqName (Custom s _) = camelCase s ++ "Eq"

ltName :: AgdaType -> String
ltName (Builtin _ _ fun) = fun
ltName (Custom s _) = camelCase s ++ "Lt"

maybeParens :: String -> String
maybeParens s = if ' ' `elem` s then "(" ++ s ++ ")" else s

makeLt :: AgdaType -> String
makeLt Builtin{} = ""
makeLt tp@(Custom name cons) =
  let def = ltName tp ++ " : " ++ name ++ " → " ++ name ++ " → Bool"
      base = [ ltName tp ++ " " ++ con ++ " " ++ con ++ " = false"
             | (con, args) <- cons
             , null args
             ]
      indu = [ ltName tp ++ " (" ++ con ++ concat [ " l" ++ show i | (i, _) <- zip [1..] args ] ++ ")"
                         ++ " (" ++ con ++ concat [ " r" ++ show i | (i, _) <- zip [1..] args ] ++ ") = "
                         ++ "isLt ("
                         ++ concat [ eqName atp ++ " l" ++ show i ++ " r" ++ show i ++ " ∷ "
                                   | (i, atp) <- zip [1..] args
                                   ]
                         ++ "[]) ("
                         ++ concat [ ltName atp ++ " l" ++ show i ++ " r" ++ show i ++ " ∷ "
                                   | (i, atp) <- zip [1..] args
                                   ]
                         ++ "[])"
             | (con, args) <- cons
             , not (null args)
             ]
      less = [ ltName tp ++ " " ++ maybeParens (con1 ++ concat [ " _" | _ <- args1 ])
                         ++ " " ++ maybeParens (con2 ++ concat [ " _" | _ <- args2 ])
                         ++ " = true"
             | (i, (con1, args1)) <- zip [1..] cons
             , (j, (con2, args2)) <- zip [1..] cons
             , i < j
             ]
      catchAll = ltName tp ++ " _ _ = false"
      maybeCatch = if length cons == 1 then [] else [catchAll]
  in unlines $ [def] ++ base ++ indu ++ less ++ maybeCatch

makeEq :: AgdaType -> String
makeEq Builtin{} = ""
makeEq tp@(Custom name cons) =
  let def = eqName tp ++ " : " ++ name ++ " → " ++ name ++ " → Bool"
      base = [ eqName tp ++ " " ++ con ++ " " ++ con ++ " = true"
             | (con, args) <- cons
             , null args
             ]
      indu = [ eqName tp ++ " (" ++ con ++ concat [ " l" ++ show i | (i, _) <- zip [1..] args ] ++ ")"
                         ++ " (" ++ con ++ concat [ " r" ++ show i | (i, _) <- zip [1..] args ] ++ ") = "
                         ++ intercalate " ∧ " [ eqName atp ++ " l" ++ show i ++ " r" ++ show i
                                              | (i, atp) <- zip [1..] args
                                              ]
             | (con, args) <- cons
             , not (null args)
             ]
      catchAll = eqName tp ++ " _ _ = false"
      maybeCatch = if length cons == 1 then [] else [catchAll]
  in unlines $ [def] ++ base ++ indu ++ maybeCatch

indent :: String -> String
indent "" = ""
indent s = "  " ++ s

boolAnd :: String
boolAnd = "\
  \infixr 6 _∧_\n\
  \_∧_ : Bool → Bool → Bool\n\
  \true ∧ true = true\n\
  \_ ∧ _ = false\n"

makeEqs :: [AgdaType] -> String
makeEqs tps0 = let tps = Map.elems $ foldl' withDeps Map.empty tps0
                   lns = "mutual" : map indent (concatMap (lines . makeEq') tps)
               in boolAnd ++ "\n" ++ unlines lns
  where
    makeEq' :: AgdaType -> String
    makeEq' Builtin{} = ""
    makeEq' tp = "\n" ++ makeEq tp


isLt :: String
isLt = "\
  \isLt : ∀ {n} → Vec Bool n → Vec Bool n → Bool\n\
  \isLt [] [] = false\n\
  \isLt (true ∷ xs) (_ ∷ ys) = isLt xs ys\n\
  \isLt (false ∷ xs) (y ∷ ys) = y\n"

makeLts :: [AgdaType] -> String
makeLts tps0 = let tps = Map.elems $ foldl' withDeps Map.empty tps0
                   lns = "mutual" : map indent (concatMap (lines . makeLt') tps)
               in isLt ++ "\n" ++ unlines lns
  where
    makeLt' :: AgdaType -> String
    makeLt' Builtin{} = ""
    makeLt' tp = "\n" ++ makeLt tp

