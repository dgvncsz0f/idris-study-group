module CH09

%default total

data Elem : a -> List a -> Type where
  InCons : Elem value (value :: xs)
  InList : (prf : Elem value xs) -> Elem value (x :: xs)

elemNotInNil : Elem value [] -> Void
elemNotInNil _ impossible

elemNotInTail : (notInTail : Elem y xs -> Void) -> (notInCons : (x = y) -> Void) -> Elem y (x :: xs) -> Void
elemNotInTail _ notInCons InCons               = notInCons Refl
elemNotInTail notInTail notInCons (InList prf) = notInTail prf

isElem : DecEq a => (value : a) -> (xs : List a) -> Dec (Elem value xs)
isElem _ []        = No elemNotInNil
isElem y (x :: xs) = case decEq x y of
                       Yes Refl     => Yes InCons
                       No notInCons => case isElem y xs of
                                         Yes prf      => Yes (InList prf)
                                         No notInTail => No (elemNotInTail notInTail notInCons)

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

notInLast : (contra : (x = y) -> Void) -> Last [x] y -> Void
notInLast contra LastOne = contra Refl

notInNil : Last [] value -> Void
notInNil _ impossible

notInTail : (notNil : (xs = []) -> Void) -> (notInList : Last xs y -> Void) -> Last (x :: xs) y -> Void
notInTail notNil _ LastOne           = notNil Refl
notInTail _ notInList (LastCons prf) = notInList prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] _        = No notInNil
isLast (x :: xs) y = case decEq xs [] of
                       Yes Refl  => case decEq x y of
                                      Yes Refl => Yes LastOne
                                      No notEq => No (notInLast notEq)
                       No notNil => case isLast xs y of
                                      Yes prf    => Yes (LastCons prf)
                                      No notLast => No (notInTail notNil notLast)
