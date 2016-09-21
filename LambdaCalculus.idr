module LambdaCalculus

%access public export


------------- 
-- Data types
-------------

data TVar = TV Nat
 
Show TVar where
  show (TV s) = show s

Eq TVar where
  (==) (TV s) (TV t) = s == t

  
data LambdaType = BaseType String
                | ArrowType LambdaType LambdaType
                | TypeVar TVar
                | Pi LambdaType


infixr 10 ->>
(->>): LambdaType -> LambdaType -> LambdaType
a ->> b = ArrowType a b

data Var: LambdaType -> Type where
  MkVar: String -> (Var type)

data MyConst: LambdaType -> Type where
  MkConst: String ->  (MyConst type)

instantiateType : LambdaType -> LambdaType -> LambdaType
instantiateType = instantiateType' 0 where
  instantiateType' : Nat -> LambdaType -> LambdaType -> LambdaType
  instantiateType' n t s@(BaseType _) = s
  instantiateType' n t (TypeVar (TV k)) = if n == k then t else TypeVar (TV k)
  instantiateType' n t (ArrowType s1 s2) = ArrowType (instantiateType' n t s1) (instantiateType' n t s2)
  instantiateType' n t (Pi s) = Pi $ instantiateType' (n+1) t s


data LambdaExpression : LambdaType -> Type where
  LambdaVar : (Var varType) -> (LambdaExpression varType)
  LambdaConst : (MyConst constType) -> (LambdaExpression constType)
  Abs : (Var dom) -> (LambdaExpression cod) -> (LambdaExpression (ArrowType dom cod))
  App : (LambdaExpression (ArrowType dom cod)) -> (LambdaExpression dom) -> (LambdaExpression cod)
  TypeAbs : (LambdaExpression t) -> (LambdaExpression (Pi t))
  TypeApp : {expr: LambdaType} -> (LambdaExpression (Pi expr)) -> (type: LambdaType) -> (LambdaExpression (instantiateType type expr))


λ: (Var dom) -> (LambdaExpression cod) -> (LambdaExpression (ArrowType dom cod))
λ = Abs

Λ: (LambdaExpression t) -> (LambdaExpression (Pi t))
Λ = TypeAbs

-----------------------
-- Implicit conversions
-----------------------

public export
implicit lambdaVar: (Var t) -> (LambdaExpression t)
lambdaVar = LambdaVar

public export
implicit lambdaConst: (MyConst t) -> (LambdaExpression t)
lambdaConst = LambdaConst

public export
implicit typeVar: TVar -> LambdaType
typeVar = TypeVar

data Substitution: LambdaType -> Type where
  Sub: {subType: LambdaType} -> (what: Var subType) -> (by: LambdaExpression subType) -> (Substitution subType)

----------------------------
-- Interface implementations
----------------------------
Show LambdaType where
  show (BaseType s) = s
  show (ArrowType t1 t2) = "(" ++ (show t1) ++ " -> " ++ (show t2) ++ ")"
  show (TypeVar s) = show s
  show (Pi t) = "Π" ++ "." ++ (show t)

Eq LambdaType where
  (==) (BaseType s) (BaseType t) = s == t
  (==) (ArrowType t11 t12) (ArrowType t21 t22) = (t11 == t21) && (t12 == t22)
  (==) (TypeVar v) (TypeVar w) = v == w
  (==) (Pi s) (Pi t) = s == t
  (==) _ _ = False

Show (Var t) where
  show (MkVar s) = s

Eq (Var t) where
  (==) (MkVar n1) (MkVar n2) = n1 == n2

Show (MyConst t) where
  show (MkConst s) = s

Eq (MyConst t) where
  (MkConst n1) ==  (MkConst n2) = n1 == n2

Show (LambdaExpression t) where
  show (LambdaVar v) = show v
  show (LambdaConst c) = show c
  show (Abs{dom=x} v exp) = "λ" ++ (show v) ++ ":" ++ (show x) ++ "." ++ (show exp)
  show (App f arg) = "(" ++ (show f) ++ " " ++ (show arg) ++ ")"
  show (TypeAbs expr) = "Λ" ++ "." ++ (show expr)
  show (TypeApp f tp) = "(" ++ (show f) ++ ")" ++ "[" ++ (show tp) ++ "]"

Show (Substitution t) where
  show (Sub what by) = "[" ++ (show what) ++ "\\" ++ (show by) ++ "]"

------------
-- Functions
------------

functionType: List LambdaType -> LambdaType -> LambdaType
functionType argTypes goalType = foldr ArrowType goalType argTypes

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
substitute {subType = x} (Sub what by) (LambdaVar {varType=x} v) = if what == v 
                                                                      then by 
                                                                      else LambdaVar v
substitute s (LambdaVar v) = LambdaVar v
substitute _ (LambdaConst c) = LambdaConst c
substitute {subType=x} {expType=z}  s (App {dom=y} {cod=z} f arg) = App {dom=y} {cod = z} fNew argNew where
  fNew = substitute {subType = x} {expType = ArrowType y z} s f
  argNew = substitute {subType = x} {expType = y}  s arg
substitute (Sub what by) (Abs (MkVar n) expr) = if what == MkVar n
                                                 then λ (MkVar n) expr
                                                 else substitute (Sub what by) (λ vNew exprNew) where 
                                                   vNew = freshVar (MkVar n) (freeVars by)
                                                   exprNew = substitute (Sub (MkVar n) (LambdaVar vNew)) expr

expType: (LambdaExpression t) -> LambdaType
expType {t} _ = t

instantiateTypeVarInVar : (t : LambdaType) -> (LambdaCalculus.Var a) -> (LambdaCalculus.Var (instantiateType t a))
instantiateTypeVarInVar {a} _ (MkVar x) = MkVar x

instantiateTypeVarInConst : (t: LambdaType) -> (LambdaCalculus.MyConst a) -> (LambdaCalculus.MyConst (instantiateType t a))
instantiateTypeVarInConst {a} _ (MkConst x) = MkConst x

--instantiateTypeVarInApp : (t: LambdaType) -> (f: LambdaExpression fType) -> (arg: LambdaExpression argType) -> LambdaExpression (ArrowType (instantiateType t fType) (instantiateType t argType))
--instantiateTypeVarInApp t f arg = App (instantiateTypeVar

instantiateTypeVar : (t: LambdaType) -> (LambdaExpression s) -> LambdaExpression (instantiateType t s) 
instantiateTypeVar tp (LambdaVar w) = LambdaVar $ instantiateTypeVarInVar tp w
instantiateTypeVar tp (LambdaConst c) = LambdaConst $ instantiateTypeVarInConst tp c
instantiateTypeVar tp (App f arg) = App (instantiateTypeVar tp f) (instantiateTypeVar tp arg)
instantiateTypeVar tp (Abs w expr) = λ (instantiateTypeVarInVar tp w) (instantiateTypeVar tp expr)
--instantiateTypeVar v tp (TypeApp f tp') = TypeApp (instantiateTypeVar v tp f) (substituteT v tp tp')

betaReduce : (LambdaExpression t) -> (LambdaExpression t)
betaReduce (App (Abs v expr) arg) = substitute (Sub v arg) expr
betaReduce (TypeApp (TypeAbs expr) t) = instantiateTypeVar t expr
betaReduce (LambdaVar v) = LambdaVar v
betaReduce (LambdaConst c) = LambdaConst c
betaReduce (App f arg) = App (betaReduce f) (betaReduce arg)
betaReduce (Abs v expr) = Abs v (betaReduce expr)
betaReduce (TypeApp f arg) = TypeApp (betaReduce f) arg
betaReduce (TypeAbs expr) = TypeAbs (betaReduce expr)

Eq (LambdaExpression t) where
 (LambdaVar v) == (LambdaVar w) = v == w
 (LambdaConst v) == (LambdaConst w) = v == w
 (App{dom}{cod} f1 arg1) == (App{dom}{cod} f2 arg2) = f1 == f2 && arg1 == arg2
 (Abs{dom}{cod} v expr1) == (Abs{dom}{cod} w expr2) = (substitute (Sub v w) expr1) == expr2
 (TypeAbs expr1) == (TypeAbs expr2) = expr1 == expr2
 (TypeApp{expr} expr1 s) == (TypeApp{expr} expr2 s) = expr1 == expr2 


