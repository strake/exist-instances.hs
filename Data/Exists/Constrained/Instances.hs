{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Data.Exists.Constrained.Instances where

import Data.Exists.Constrained
import Data.Constraint
import Data.Constraint.Lifting
import Data.Type.Equality
import Type.Reflection

instance (Typeable a, Lifting c Eq a) => Eq (E c a) where
    E a == E b =
        (\ (Refl :: a i :~: a j) -> case (lift :: c i :- Eq (a i)) of Sub Dict -> a == b) `any`
        testEquality (typeOf a) (typeOf b)

instance (Typeable a, Lifting c Eq a, Lifting c Ord a) => Ord (E c a) where
    compare (E (a :: a i)) (E b)
      | Just (Refl :: a i :~: a j) <- testEquality s t
      , Sub Dict <- lift :: c i :- Ord (a i) = compare a b
      | otherwise = compare (SomeTypeRep s) (SomeTypeRep t)
      where (s, t) = (typeOf a, typeOf b)

instance (Lifting c Show a) => Show (E c a) where
    showsPrec n (E (a :: a i)) | Sub Dict <- lift :: c i :- Show (a i) = showsPrec n a
