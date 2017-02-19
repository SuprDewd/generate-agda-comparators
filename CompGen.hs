module CompGen ( AgdaType(..)
               , Var
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

type Var = String
type TypeName = String
type ConstructorName = String
type FunctionName = String

data AgdaType = Custom [Var] TypeName [(ConstructorName, [AgdaType])]
              | Builtin [Var] TypeName FunctionName FunctionName
              deriving (Show)

typeName :: AgdaType -> TypeName
typeName (Custom _ name _) = name
typeName (Builtin _ name _ _) = name

withDeps :: Map.Map TypeName AgdaType -> AgdaType -> Map.Map TypeName AgdaType
withDeps deps tp@(Builtin _ name _ _) = Map.insertWith const name tp deps
withDeps deps tp@(Custom _ name cons)
  | name `Map.member` deps = deps
  | otherwise              = foldl' withDeps (Map.insert name tp deps) (concatMap snd cons)

camelCase :: TypeName -> String
camelCase s = toLower (head s) : filter (not . (`elem` "() ")) (tail s)

injName :: TypeName -> ConstructorName -> Int -> String
injName s con i = camelCase s ++ "-" ++ con ++ "-inj" ++ show i

eqName :: AgdaType -> String
eqName (Builtin _ _ fun _) = fun
eqName (Custom _ s _) = camelCase s ++ "Eq"

ltName :: AgdaType -> String
ltName (Builtin _ _ _ fun) = fun
ltName (Custom _ s _) = camelCase s ++ "Lt"

maybeParens :: String -> String
maybeParens s = if ' ' `elem` s then "(" ++ s ++ ")" else s

makeLt :: AgdaType -> String
makeLt Builtin{} = ""
makeLt tp@(Custom vs name cons) =
  let def = ltName tp ++ " : " ++ quants vs ++ "(p q : " ++ name ++ ") → Bool"
      base = [ ltName tp ++ " " ++ con ++ " " ++ con ++ " = false"
             | (con, args) <- cons
             , null args
             ]
      indu = [ ltName tp ++ " (" ++ con ++ concat [ " l" ++ show i | (i, _) <- zip [1..] args ] ++ ")"
                         ++ " (" ++ con ++ concat [ " r" ++ show i | (i, _) <- zip [1..] args ] ++ ") = "
                         ++ "isLt ("
                         ++ concat [ "toBool (" ++ eqName atp ++ " l" ++ show i ++ " r" ++ show i ++ ") ∷ "
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

makeInj :: AgdaType -> Int -> Int -> String
makeInj Builtin{} _ _ = ""
makeInj (Custom vs name cons) i j =
  let (con, tps) = cons !! i
  in injName name con (j+1) ++ " : " ++ quants vs
     ++ concat [ "∀ {l" ++ show k ++ " r" ++ show k ++ " : " ++ typeName tp ++ "} → "
               | (k, tp) <- zip [1..] tps
               ]
     ++ con ++ concat [ " l" ++ show k | k <- [1..length tps] ]
     ++ " P≡ "
     ++ con ++ concat [ " r" ++ show k | k <- [1..length tps] ]
     ++ " → l" ++ show (j+1) ++ " P≡ r" ++ show (j+1) ++ "\n"
     ++ injName name con (j+1) ++ " Prefl = Prefl"

makeInjs :: AgdaType -> String
makeInjs Builtin{} = ""
makeInjs tp@(Custom _ _ cons) =
  let lns = concat [ lines $ makeInj tp i j
                   | i <- [0..length cons - 1]
                   , j <- [0..length (snd $ cons !! i) - 1]
                   ]
  in unlines lns

quants :: [Var] -> String
quants [] = ""
quants xs = "∀ {" ++ unwords xs ++ "} → "

makeEq :: AgdaType -> String
makeEq Builtin{} = ""
makeEq tp@(Custom vs name cons) =
  let def = eqName tp ++ " : " ++ quants vs ++ "(p q : " ++ name ++ ") → Dec (p P≡ q)"
      base = [ eqName tp ++ " " ++ con ++ " " ++ con ++ " = yes Prefl"
             | (con, args) <- cons
             , null args
             ]
      indu = [ eqName tp ++ " (" ++ con ++ concat [ " l" ++ show i | (i, _) <- zip [1..] args ] ++ ")"
                         ++ " (" ++ con ++ concat [ " r" ++ show i | (i, _) <- zip [1..] args ] ++ ") with "
                         ++ intercalate " | " [ eqName atp ++ " l" ++ show i ++ " r" ++ show i
                                              | (i, atp) <- zip [1..] args
                                              ]
               ++ concat [ "\n" ++ eqName tp ++ " (" ++ con ++ concat [ " l" ++ show i | (i, _) <- zip [1..] args ] ++ ")"
                           ++ " (" ++ con ++ concat [ " " ++ (if i > j then "r" else ".l") ++ show i
                                                    | (i, _) <- zip [1..] args ] ++ ")"
                           ++ concat [ " | " ++ (if i == j then "no ¬p"
                                                else if i < j then "yes Prefl"
                                                else "_")
                                     | (i, _) <- zip [0..] args ]
                           ++ " = " ++ (if j == length args then "yes Prefl"
                                        else "no (λ p → ¬p (" ++ injName name con (j+1) ++ " p))")
                         | j <- [0..length args]
                         ]
             | (con, args) <- cons
             , not (null args)
             ]
      diff = [ eqName tp ++ " (" ++ con1 ++ concat [ " _" | _ <- args1 ] ++ ")"
                         ++ " (" ++ con2 ++ concat [ " _" | _ <- args2 ] ++ ") = no (λ ())"
             | (con1, args1) <- cons
             , (con2, args2) <- cons
             , con1 /= con2
             ]
  in unlines $ [def] ++ base ++ indu ++ diff

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
                   pri = "private" : map indent (concatMap (lines . makeInjs') tps)
                   mut = "mutual" : map indent (concatMap (lines . makeEq') tps)
               in boolAnd ++ "\n" ++ unlines pri ++ "\n" ++ unlines mut
  where
    makeEq' :: AgdaType -> String
    makeEq' Builtin{} = ""
    makeEq' tp = "\n" ++ makeEq tp

    makeInjs' :: AgdaType -> String
    makeInjs' Builtin{} = ""
    makeInjs' tp = "\n" ++ makeInjs tp


isLt :: String
isLt = "\
  \isLt : ∀ {n} → Vec Bool n → Vec Bool n → Bool\n\
  \isLt [] [] = false\n\
  \isLt (true ∷ xs) (_ ∷ ys) = isLt xs ys\n\
  \isLt (false ∷ xs) (y ∷ ys) = y\n"

toBool :: String
toBool = "\
  \toBool : ∀ {a} {A : Set a} → {x y : A} → Dec (x P≡ y) → Bool\n\
  \toBool (yes _) = true\n\
  \toBool (no _) = false\n"

makeLts :: [AgdaType] -> String
makeLts tps0 = let tps = Map.elems $ foldl' withDeps Map.empty tps0
                   lns = "mutual" : map indent (concatMap (lines . makeLt') tps)
               in isLt ++ "\n"
                  ++ toBool ++ "\n"
                  ++ unlines lns
  where
    makeLt' :: AgdaType -> String
    makeLt' Builtin{} = ""
    makeLt' tp = "\n" ++ makeLt tp

