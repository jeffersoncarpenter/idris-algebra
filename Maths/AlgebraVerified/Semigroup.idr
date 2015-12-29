module Maths.AlgebraVerified.Semigroup

import Maths.AlgebraVerified.Magma

%access public

||| A magma whose operation is associative
|||
class (Magma a op) => Semigroup a (op : a -> a -> a) | a where
  opAssociative : (x : a) -> (y : a) -> (z : a) -> x `op` (y `op` z) = (x `op` y) `op` z


instance Maths.AlgebraVerified.Semigroup.Semigroup Nat Nat.plus where
  opAssociative = plusAssociative
