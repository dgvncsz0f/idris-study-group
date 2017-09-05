module CH06

import Data.Vect

Matrix : Nat -> Nat -> Type
Matrix x y = Vect x (Vect y Int)

testMatrix : Matrix 2 3
testMatrix = [[0,0,0], [0,0,0]]

TupleVect : (n : Nat) -> Type -> Type
TupleVect Z ty     = ()
TupleVect (S n) ty = (ty, (TupleVect n ty))

testTupleVect : TupleVect 4 Nat
testTupleVect = (1,2,3,4,())
