module CH11

import Data.Primitives.Views

every_other : Stream Int -> Stream Int
every_other (_ :: x :: xs) = x :: every_other xs

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

implementation Functor InfList where
  -- map : (a -> b) -> InfList a -> InfList b
  map f (value :: inflist) = f value :: map f inflist

%name InfList xs, ys, zs

countFrom : Integer -> InfList Integer
countFrom x = x :: Delay (countFrom (x + 1))

getPrefix : Nat -> InfList a -> List a
getPrefix Z xs            = []
getPrefix (S k) (x :: xs) = x :: getPrefix k xs

data Face = Head | Tail

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223
               in (seed' `shiftR` 2) :: randoms seed'

getFace : Int -> Face
getFace n with (divides n 2)
  getFace (2 * q + r) | DivBy prf = if r == 0 then Head else Tail

coinFlips : Nat -> Stream Int -> List Face
coinFlips Z xs            = []
coinFlips (S k) (x :: xs) = getFace x :: coinFlips k xs
