module Main where

import CompGen

string :: AgdaType
string = Builtin "String" "primStringEquality" "primStringLess"

float :: AgdaType
float = Builtin "Float" "primFloatEquality" "primFloatLess"

char :: AgdaType
char = Builtin "Char" "primCharEquality" "primCharLess"

nat :: AgdaType
nat = Custom "Nat"
             [ ("zero", [])
             , ("suc", [nat])
             ]

list :: AgdaType -> AgdaType
list a = Custom ("List " ++ maybeParens (typeName a))
                [ ("[]", [])
                , ("_∷_", [a, list a])
                ]

-- postulate Name : Set
-- primQNameEquality : Name → Name → Bool
name :: AgdaType
name = Builtin "Name" "primQNameEquality" "primQNameLess"

-- data Visibility : Set where
--   visible hidden instance′ : Visibility
visibility :: AgdaType
visibility = Custom "Visibility"
                    [ ("visible", [])
                    , ("hidden", [])
                    , ("instance′", [])
                    ]

-- data Relevance : Set where
--   relevant irrelevant : Relevance
relevance :: AgdaType
relevance = Custom "Relevance"
                   [ ("relevant", [])
                   , ("irrelevant", [])
                   ]

-- data Abs (A : Set) : Set where
--   abs : (s : String) (x : A) → Abs A
ab :: AgdaType -> AgdaType
ab a = Custom ("Abs " ++ maybeParens (typeName a))
              [ ("abs", [string, a])
              ]

-- data ArgInfo : Set where
--   arg-info : (v : Visibility) (r : Relevance) → ArgInfo
argInfo :: AgdaType
argInfo = Custom "ArgInfo"
                 [ ("arg-info", [visibility, relevance])
                 ]

-- data Arg (A : Set) : Set where
--   arg : (i : ArgInfo) (x : A) → Arg A
arg :: AgdaType -> AgdaType
arg a = Custom ("Arg " ++ maybeParens (typeName a))
               [ ("arg", [argInfo, a])
               ]

-- postulate Meta : Set
-- primMetaEquality : Meta → Meta → Bool
meta :: AgdaType
meta = Builtin "Meta" "primMetaEquality" "primMetaLess"

-- data Literal : Set where
--   nat    : (n : Nat)    → Literal
--   float  : (x : Float)  → Literal
--   char   : (c : Char)   → Literal
--   string : (s : String) → Literal
--   name   : (x : Name)   → Literal
--   meta   : (x : Meta)   → Literal
literal :: AgdaType
literal = Custom "Literal"
                 [ ("nat", [nat])
                 , ("float", [float])
                 , ("char", [char])
                 , ("string", [string])
                 , ("name", [name])
                 , ("meta", [meta])
                 ]

-- data Pattern : Set where
--   con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
--   dot    : Pattern
--   var    : (s : String)  → Pattern
--   lit    : (l : Literal) → Pattern
--   proj   : (f : Name)    → Pattern
--   absurd : Pattern
pat :: AgdaType
pat = Custom "Pattern"
             [ ("con", [name, list (arg pat)])
             , ("dot", [])
             , ("var", [string])
             , ("lit", [literal])
             , ("proj", [name])
             , ("absurd", [])
             ]

-- data Term : Set
-- data Sort : Set
-- data Clause : Set
-- Type = Term
typ :: AgdaType
typ = term

-- data Term where
--   var       : (x : Nat) (args : List (Arg Term)) → Term
--   con       : (c : Name) (args : List (Arg Term)) → Term
--   def       : (f : Name) (args : List (Arg Term)) → Term
--   lam       : (v : Visibility) (t : Abs Term) → Term
--   pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term
--   pi        : (a : Arg Type) (b : Abs Type) → Term
--   agda-sort : (s : Sort) → Term
--   lit       : (l : Literal) → Term
--   meta      : (x : Meta) → List (Arg Term) → Term
--   unknown   : Term -- Treated as '_' when unquoting.
term :: AgdaType
term = Custom "Term"
              [ ("var", [nat, list (arg term)])
              , ("con", [name, list (arg term)])
              , ("def", [name, list (arg term)])
              , ("lam", [visibility, ab term])
              , ("pat-lam", [list clause, list (arg term)])
              , ("pi", [arg typ, ab typ])
              , ("agda-sort", [sort])
              , ("lit", [literal])
              , ("meta", [meta, list (arg term)])
              , ("unknown", [])
              ]

-- data Sort where
--   set     : (t : Term) → Sort -- A Set of a given (possibly neutral) level.
--   lit     : (n : Nat) → Sort  -- A Set of a given concrete level.
--   unknown : Sort
sort :: AgdaType
sort = Custom "Sort"
              [ ("set", [term])
              , ("lit", [nat])
              , ("unknown", [])
              ]

-- data Clause where
--   clause        : (ps : List (Arg Pattern)) (t : Term) → Clause
--   absurd-clause : (ps : List (Arg Pattern)) → Clause
clause :: AgdaType
clause = Custom "Clause"
                [ ("clause", [list (arg pat), term])
                , ("absurd-clause", [list (arg pat)])
                ]

-- data Definition : Set where
--   function    : (cs : List Clause) → Definition
--   data-type   : (pars : Nat) (cs : List Name) → Definition  -- parameters and constructors
--   record-type : (c : Name) → Definition                     -- name of data/record type
--   data-cons   : (d : Name) → Definition                     -- name of constructor
--   axiom       : Definition
--   prim-fun    : Definition
definition :: AgdaType
definition = Custom "Definition"
                    [ ("function", [list clause])
                    , ("data-type", [nat, list name])
                    , ("record-type", [name])
                    , ("data-cons", [name])
                    , ("axiom", [])
                    , ("prim-fun", [])
                    ]

main :: IO ()
main = do
  let arr = [term]
  putStr $ makeEqs arr
  putStrLn ""
  putStr $ makeLts arr

