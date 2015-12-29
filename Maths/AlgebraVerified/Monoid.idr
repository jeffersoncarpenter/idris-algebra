module Maths.AlgebraVerified.Monoid

import Maths.AlgebraVerified.Semigroup

%access public

||| A magma whose operation is associative
|||
class (Semigroup a op) => Monoid a (op : a -> a -> a) (id : a) | a where
  identityLeft : (x : a) -> op id x = x
  identityRight : (x : a) -> op x id = x


instance Maths.AlgebraVerified.Monoid.Monoid Nat Nat.plus Nat.Z where
  identityLeft = plusZeroLeftNeutral
  identityRight = plusZeroRightNeutral
