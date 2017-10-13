module CH10_1

import Data.Vect
import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix = go []
  where
    go : Eq a => List a -> List a -> List a -> List a
    go acc xs ys with (snocList xs)
      go acc [] _ | Empty = []
      go acc (xs ++ [x]) ys | (Snoc xsrev) with (snocList ys)
        go acc (xs ++ [x]) [] | (Snoc xsrev) | Empty = acc
        go acc (xs ++ [x]) (ys ++ [y]) | (Snoc xsrev) | (Snoc ysrev) =
          if x == y
          then go (x :: acc) xs ys | xsrev | ysrev
          else acc

mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SlitRecOne = [x]
  mergeSort (left ++ right) | (SplitRecPair leftView rightView) =
    merge (mergeSort left | leftView) (mergeSort right | rightView)

toBinary : Nat -> String
toBinary = go ""
  where
    go : String -> Nat -> String
    go acc n with (halfRec n)
      go acc Z | HalfRecZ = acc
      go acc (S (n + n)) | (HalfRecOdd nrec) = go (strCons '1' acc) n | nrec
      go acc (n + n) | (HalfRecEven nrec) = go (strCons '0' acc) n | nrec

palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | Vnil = True
  palindrome [x] | (VOne) = True
  palindrome (x :: xs ++ [y]) | (VCons xsrec) =
    if x == y
    then palindrome xs | xsrec
    else False
