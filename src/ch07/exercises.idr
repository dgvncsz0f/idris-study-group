module CH07

data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

area : Shape -> Double
area (Triangle x y) = x * y / 2
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x)   = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x)   = abs (eval x)

Eq Shape where
  (Triangle x0 y0) == (Triangle x1 y1)   = x0 == x1 && y0 == y1
  (Rectangle x0 y0) == (Rectangle x1 y1) = x0 == x1 && y0 == y1
  (Circle x0) == (Circle x1)             = x0 == x1
  _ == _                                 = False

Ord Shape where
  compare shape0 shape1 = compare (area shape0) (area shape1)

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub
  abs = Abs

Show ty => Show (Expr ty) where
  show (Val n)   = show n
  show (Add l r) = "(" ++ show l ++ " + " ++ show r ++ ")"
  show (Sub l r) = "(" ++ show l ++ " - " ++ show r ++ ")"
  show (Mul l r) = "(" ++ show l ++ " * " ++ show r ++ ")"
  show (Div l r) = "(" ++ show l ++ " / " ++ show r ++ ")"
  show (Abs e)   = "(abs " ++ show e ++ ")"

(Neg ty, Integral ty, Eq ty) => Eq (Expr ty) where
  l == r = (eval l) == (eval r)

(Neg from_ty, Integral from_ty) => Cast (Expr from_ty) from_ty where
  cast expr = eval expr

Functor Expr where
  map f (Val n)   = Val $ f n
  map f (Add l r) = Add (map f l) (map f r)
  map f (Sub l r) = Sub (map f l) (map f r)
  map f (Mul l r) = Mul (map f l) (map f r)
  map f (Div l r) = Div (map f l) (map f r)
  map f (Abs e)   = Abs $ map f e

Functor (Vect n) where
  map f Nil       = Nil
  map f (x :: xs) = f x :: map f xs

Foldable (Vect n) where
  foldr f acc Nil       = acc
  foldr f acc (x :: xs) = f x (foldr f acc xs)

  foldl f acc Nil       = acc
  foldl f acc (x :: xs) = foldl f (f acc x) xs

Eq e => Eq (Vect n e) where
  Nil == Nil             = True
  (x :: xs) == (y :: ys) = x == y && xs == ys
