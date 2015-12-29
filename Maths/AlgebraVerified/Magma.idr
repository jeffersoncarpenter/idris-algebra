module Maths.AlgebraVerified.Magma

%access public

||| A type equipped with a binary operation
|||
class Magma a (op : a -> a -> a) | a where

instance Magma Nat Nat.plus where
