module CH08

data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

data ThreeEq : a -> b -> c -> Type where
  ThreeSame : ThreeEq x x x

cong2 : { f : x -> y -> z} -> a = b -> c = d -> f a c = f b d
cong2 Refl Refl = Refl

same_cons : {xs : List a} -> {ys : List a}
          -> xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

same_lists : {xs : List a} -> {ys : List a}
           -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x ThreeSame = ThreeSame

myPlusCommutes : (n : Nat) -> (m: Nat) -> n + m = m + n
myPlusCommutes Z m     = rewrite (plusZeroRightNeutral m) in Refl
myPlusCommutes (S k) m = rewrite myPlusCommutes k m
                         in plusSuccRightSucc m k

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where
    reverse' : Vect k a -> Vect m a -> Vect (k + m) a
    reverse' {k} acc []                  = rewrite (plusZeroRightNeutral k) in acc
    reverse' {k} {m = S m} acc (x :: xs) = rewrite sym (plusSuccRightSucc k m)
                                           in (reverse' (x :: acc) xs)

headUnequal : DecEq a => {xs : Vect n a}
                      -> {ys : Vect n a}
                      -> (contra: (x = y) -> Void)
                      -> ((x :: xs) = (y :: ys))
                      -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a}
                      -> {ys : Vect n a}
                      -> (contra: (xs = ys) -> Void)
                      -> ((x :: xs) = (y :: ys))
                      -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vect n a) where
  decEq [] []               = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
                                Yes Refl  => case decEq xs ys of
                                               Yes Refl  => Yes Refl
                                               No contra => No (tailUnequal contra)
                                No contra => No (headUnequal contra)
