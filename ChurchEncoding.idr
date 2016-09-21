module ChurchEncoding

import LambdaCalculus

%access public export


tx: TVar
tx = TV "X"

ty: TVar
ty = TV "Y"

tz: TVar
tz = TV "Z"

x: Var tx
x = MkVar "x"

y: Var tx
y = MkVar "y"

ctor: List LambdaType -> LambdaType
ctor ts = functionType ts tx

churchEncoding: List (List LambdaType) -> LambdaType
churchEncoding ts = Pi tx $ ctor (map ctor ts)

export
bool: LambdaType
bool = churchEncoding [Nil, Nil] 

public export
true: LambdaExpression ChurchEncoding.bool
true = TypeAbs tx true' where
  true': LambdaExpression (tx ->> tx ->> tx)
  true' = λ x (λ y x)

public export
false: LambdaExpression ChurchEncoding.bool
false = Λ tx false' where
  false': LambdaExpression(tx ->> tx ->> tx)
  false' = λ x (λ y y)

export
ite: LambdaExpression (Pi ChurchEncoding.ty $ ChurchEncoding.bool ->> ChurchEncoding.ty ->> ChurchEncoding.ty ->> ChurchEncoding.ty ) 
ite = let b = (MkVar{type=bool} "b") 
          t = (MkVar{type=ty} "t")
          f = (MkVar{type=ty} "f")
      in Λ ty $ λ b $ λ t $ λ f $ ?hole --((b `TypeApp` ty) `App` t) `App` f where
--ite: (LambdaExpression ChurchEncoding.bool) -> (LambdaExpression a) -> (LambdaExpression a) -> LambdaExpression a
--ite {a} b t f = betaReduce $ App (App (TypeApp b a) t) f

-- pair a b = ΠX.(a -> b -> X) -> X
prod: LambdaType -> LambdaType -> LambdaType
prod a b = churchEncoding [[a, b]]

mkProd: LambdaExpression(Pi ty $ Pi tz $ ty --> tz --> (prod ty tz)) 
mkProd = Λ ty $ Λ tz $ λ y $ λ z $ ?hole
--mkProd: LambdaExpression a -> LambdaExpression b -> LambdaExpression (prod a b)
--mkProd x y = TypeAbs tx $ Abs (MkVar "f") $ ((MkVar "f") `App` x) `App` y

fst: LambdaExpression (prod a b) -> LambdaExpression a
fst {a} pair = App (TypeApp pair a) fst' where
  fst' = Abs (MkVar "x") $ Abs (MkVar "y") (MkVar "x")

snd: LambdaExpression (prod a b) -> LambdaExpression b
snd {b} pair = App (TypeApp pair b) snd' where
  snd' = Abs (MkVar "x") $ Abs (MkVar "y") (MkVar "y")


list: LambdaType -> LambdaType
list a = churchEncoding [Nil, [a]]

nil: LambdaExpression (Pi ChurchEncoding.ty $ list ChurchEncoding.ty)
nil = TypeAbs ty $ TypeAbs tx $ Abs (MkVar "z") $ Abs (MkVar "c") $ MkVar "z"

--cons: LambdaExpression
