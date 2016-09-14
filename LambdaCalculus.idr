module LambdaCalculus

%access public export

------------- 
-- Data types
-------------

data TVar = TV String
   
data LambdaType = BaseType String
                | ArrowType LambdaType LambdaType
                | TypeVar TVar
                | Pi TVar LambdaType

data Var: LambdaType -> Type where
  MkVar: String -> (Var type)

data MyConst: LambdaType -> Type where
  MkConst: String ->  (MyConst type)

data LambdaExpression: LambdaType -> Type where
  LambdaVar: (Var varType) -> (LambdaExpression varType)
  LambdaConst: (MyConst constType) -> (LambdaExpression constType)
  Abs: (Var dom) -> (LambdaExpression cod) -> (LambdaExpression (ArrowType dom cod))
  App: (LambdaExpression (ArrowType dom cod)) -> (LambdaExpression dom) -> (LambdaExpression cod)
  TypeAbs: (x: TVar) -> (LambdaExpression t) -> (LambdaExpression (Pi x t))
--  TypeApp: (LambdaExpression (Pi x t)) -> (s: LambdaType) -> (LambdaExpression (substituteT x s t))

data Substitution: LambdaType -> Type where
  Sub: {subType: LambdaType} -> (what: Var subType) -> (by: LambdaExpression subType) -> (Substitution subType)

----------------------------
-- Interface implementations
----------------------------

Show TVar where
  show (TV s) = s

Eq TVar where
  (==) (TV s) (TV t) = s == t

Show LambdaType where
  show (BaseType s) = s
  show (ArrowType t1 t2) = (show t1) ++ " -> " ++ (show t2)
  show (TypeVar s) = show s
  show (Pi v t) = "Π" ++ (show v) ++ "." ++ (show t)

Eq LambdaType where
  (==) (BaseType s) (BaseType t) = s == t
  (==) (ArrowType t11 t12) (ArrowType t21 t22) = (t11 == t21) && (t12 == t22)
  (==) (TypeVar v) (TypeVar w) = v == w
  (==) (Pi v s) (Pi w t) = (v == w) && (s == t)
  (==) _ _ = False

Show (Var t) where
  show (MkVar s) = s

Eq (Var t) where
  (==) (MkVar n1) (MkVar n2) = n1 == n2

Show (MyConst t) where
  show (MkConst s) = s

Eq (MyConst t) where
  (==) (MkConst n1) (MkConst n2) = n1 == n2

Show (LambdaExpression t) where
  show (LambdaVar v) = show v
  show (LambdaConst c) = show c
  show (Abs{dom=x} v exp) = "λ" ++ (show v) ++ ":" ++ (show x) ++ "." ++ (show exp)
  show (App f arg) = (show f) ++ " " ++ (show arg)

Show (Substitution t) where
  show (Sub what by) = "[" ++ (show what) ++ "\\" ++ (show by) ++ "]"

------------
-- Functions
------------

--substituteT: TVar -> LambdaType -> LambdaType -> LambdaType
--substituteT = ?todo

freeVars: (LambdaExpression t) -> (List (Var a))
freeVars (LambdaVar (MkVar n)) = [MkVar n]
freeVars (LambdaVar _) = []
freeVars (LambdaConst _) = []
freeVars (Abs (MkVar n) expr) = delete (MkVar n) $ nub (freeVars expr)
freeVars (Abs v expr) = nub $ freeVars expr
freeVars (App f arg) = nub $ (freeVars f) ++ (freeVars arg)

isFreeIn: (Var a) -> (LambdaExpression t) -> Bool
isFreeIn v expr = v `elem` (freeVars expr)


boundVars: (LambdaExpression t) -> List (Var a)
boundVars (Abs (MkVar n) expr) = [MkVar n]
boundVars (Abs v expr) = []
boundVars (App f arg) = nub $ (boundVars f) ++ (boundVars arg)
boundVars _ = []

isBoundIn: (Var a) -> (LambdaExpression _) -> Bool
isBoundIn v expr = v `elem` (boundVars expr)

freshVar: (Var a) -> (List (Var a)) -> (Var a)
freshVar v@(MkVar n) [] = v
freshVar v (x :: xs) with (v == x)
  | True = freshVar vNew xs where
    vNew = case v of
               (MkVar n) => MkVar (n ++ "'")
  | False = freshVar v xs

substitute: (Substitution subType) -> (LambdaExpression expType) -> (LambdaExpression expType)
substitute {subType = x} (Sub what by) (LambdaVar {varType=x} v) with (what == v)
  | True = by
  | False = LambdaVar v
substitute s (LambdaVar v) = LambdaVar v
substitute _ (LambdaConst c) = LambdaConst c
substitute {subType=x} {expType=z}  s (App {dom=y} {cod=z} f arg) = App {dom=y} {cod = z} fNew argNew where
  fNew = substitute {subType = x} {expType = ArrowType y z} s f
  argNew = substitute {subType = x} {expType = y}  s arg
substitute (Sub what by) (Abs (MkVar n) expr) with (what == MkVar n)
  | True = Abs (MkVar n) expr
  | False = substitute (Sub what by) (Abs vNew exprNew) where
    vNew = freshVar (MkVar n) (freeVars by)
    exprNew = substitute (Sub (MkVar n) (LambdaVar vNew)) expr        

--betaReduce: (LambdaExpression t) -> (LambdaExpression t)
--betaReduce 

-----------------------
-- Implicit conversions
-----------------------

implicit lambdaVar: (Var t) -> (LambdaExpression t)
lambdaVar = LambdaVar

implicit lambdaConst: (MyConst t) -> (LambdaExpression t)
lambdaConst = LambdaConst

implicit typeVar: TVar -> LambdaType
typeVar = TypeVar
