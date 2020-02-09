-- |
-- Module:      Cantor.Huge
-- Copyright:   (c) 2020 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>

{-# LANGUAGE LambdaCase #-}

module Cantor.Huge
  ( Huge
  , pow
  , evalWith
  ) where

import Prelude hiding ((^^))
import Control.Exception
import Math.NumberTheory.Logarithms
import Math.NumberTheory.Roots
import Numeric.Natural

-- | Lazy huge numbers with an efficient 'Ord' instance.
data Huge
  = Nat Natural
  | Add Huge Huge
  | Mul Huge Huge
  | Pow Huge Huge

instance Show Huge where
  show = \case
    Nat n -> show n
    Add x y -> "(" ++ show x ++ " + " ++ show y ++ ")"
    Mul x y -> "(" ++ show x ++ " * " ++ show y ++ ")"
    Pow x y -> "(" ++ show x ++ " ^ " ++ show y ++ ")"

instance Num Huge where
  (+) = add
  (*) = mul
  abs = id
  signum = const 1
  negate = throw Underflow
  fromInteger = Nat . fromInteger

{-# RULES "Huge/pow" forall x p. x ^ p = x `pow` p #-}

add :: Huge -> Huge -> Huge
add (Nat 0) y = y
add x (Nat 0) = x
-- add (Nat x) (Nat y) = Nat $ x + y
add x y = Add x y

mul :: Huge -> Huge -> Huge
mul (Nat 0) _ = Nat 0
mul _ (Nat 0) = Nat 0
mul (Nat 1) y = y
mul x (Nat 1) = x
-- mul (Nat x) (Nat y) = Nat $ x * y
mul x y = Mul x y

-- | Exponentiation.
pow :: Huge -> Huge -> Huge
pow _ (Nat 0) = Nat 1
pow (Nat 0) _ = Nat 0
pow x (Nat 1) = x
pow (Nat 1) _ = Nat 1
pow x y = Pow x y

-- | Convert 'Huge' to another numeric type,
-- using provided function for exponentiation.
evalWith :: Num a => (a -> a -> a) -> Huge -> a
evalWith (^^) = go
  where
    go = \case
      Nat n   -> fromIntegral n
      Add x y -> go x +  go y
      Mul x y -> go x *  go y
      Pow x y -> go x ^^ go y

-- | Simply 'evalWith' '(^)'.
eval :: Huge -> Natural
eval = evalWith (^)

instance Eq Huge where
  x == y = x `compare` y == EQ

instance Ord Huge where
  x `compare` y = x `compareHuge` y

-- Assuming the second argument has been constructed
-- using smart constructors.
compareNat :: Natural -> Huge -> Ordering
compareNat m = go
  where
    go = \case
      Nat n -> m `compare` n
      Add x y
        | Nat n <- x -> if m < n then LT else (m - n) `compareNat` y
        | Nat n <- y -> if m < n then LT else (m - n) `compareNat` x
        | go x == LT -> LT
        | go y == LT -> LT
        | x <= y     -> (m - eval x) `compareNat` y
        | otherwise  -> (m - eval y) `compareNat` x
      Mul x y
        | Nat n <- x -> if m < n then LT else unwrap quotPerf m n y
        | Nat n <- y -> if m < n then LT else unwrap quotPerf m n x
        | go x /= GT -> LT
        | go y /= GT -> LT
        | x <= y     -> unwrap quotPerf m (eval x) y
        | otherwise  -> unwrap quotPerf m (eval y) x
      Pow x y
        | Nat n <- x -> if m < n then LT else unwrap logPerf  m n y
        | Nat n <- y -> if m < n then LT else unwrap rootPerf m n x
        | go x /= GT -> LT
        | go y /= GT -> LT
        | x <= y     -> unwrap logPerf  m (eval x) y
        | otherwise  -> unwrap rootPerf m (eval y) x

data Perfectness = Perfect | Imperfect
  deriving (Eq, Ord, Show)

unwrap
  :: (Natural -> Natural -> (Natural, Perfectness))
  -> Natural
  -> Natural
  -> Huge
  -> Ordering
unwrap f m n y = case m `f` n of
  (q, r) -> q `compareNat` y <> (r `compare` Perfect)

quotPerf :: Natural -> Natural -> (Natural, Perfectness)
quotPerf m x = (q, r)
  where
    q = m `quot` x
    r = if q * x == m then Perfect else Imperfect

rootPerf :: Natural -> Natural -> (Natural, Perfectness)
rootPerf m x = (q, r)
  where
    q = integerRoot x m
    r = if q ^ x == m then Perfect else Imperfect

logPerf :: Natural -> Natural -> (Natural, Perfectness)
logPerf m x = (fromIntegral q, r)
  where
    q = naturalLogBase x m
    r = if x ^ q == m then Perfect else Imperfect

inverse :: Ordering -> Ordering
inverse = \case
  LT -> GT
  EQ -> EQ
  GT -> LT

-- Assuming both arguments have been constructed
-- using smart constructors.
compareHuge :: Huge -> Huge -> Ordering
Nat m   `compareHuge` z       = compareNat m z
z       `compareHuge` Nat m   = inverse $ compareNat m z
Add x y `compareHuge` Add u v = compareAddAdd x y u v
Add x y `compareHuge` Mul u v = compareAscNodes Add Mul x y u v
Add x y `compareHuge` Pow u v = compareAscNodes Add Pow x y u v
Mul x y `compareHuge` Add u v = inverse $ compareAscNodes Add Mul u v x y
Mul x y `compareHuge` Mul u v = compareMulMul x y u v
Mul x y `compareHuge` Pow u v = compareAscNodes Mul Pow x y u v
Pow x y `compareHuge` Add u v = inverse $ compareAscNodes Add Pow u v x y
Pow x y `compareHuge` Mul u v = inverse $ compareAscNodes Mul Pow u v x y
Pow x y `compareHuge` Pow u v = comparePowPow x y u v

-- Compare Add vs. Mul, Add vs. Pow or Mul vs. Pow,
-- but not vice versa.
compareAscNodes
  :: (Huge -> Huge -> Huge)
  -> (Huge -> Huge -> Huge)
  -> Huge
  -> Huge
  -> Huge
  -> Huge
  -> Ordering
compareAscNodes fxy fuv x y u v =
  case (x `compare` u, x `compare` v, y `compare` u, y `compare` v) of
    (LT,  _,  _, LT) -> LT
    ( _, LT, LT,  _) -> LT

    (GT, GT,  _,  _) -> uvSimpler
    (GT,  _,  _, GT) -> uvSimpler
    ( _, GT, GT,  _) -> uvSimpler
    ( _,  _, GT, GT) -> uvSimpler

    (LT,  _, LT,  _) -> xySimpler
    (LT,  _, EQ,  _) -> xySimpler
    (EQ,  _, LT,  _) -> xySimpler
    (EQ,  _, EQ,  _) -> xySimpler

    ( _, LT,  _, LT) -> xySimpler
    ( _, LT,  _, EQ) -> xySimpler
    ( _, EQ,  _, LT) -> xySimpler
    ( _, EQ,  _, EQ) -> xySimpler
  where
    uvSimpler = inverse $ compareNat (eval (fuv u v)) (fxy x y)
    xySimpler = compareNat (eval (fxy x y)) (fuv u v)

compareAddAdd :: Huge -> Huge -> Huge -> Huge -> Ordering
compareAddAdd x y u v =
  case (x `compare` u, x `compare` v, y `compare` u, y `compare` v) of
    (EQ,  _,  _, yv) -> yv
    ( _, EQ, yu,  _) -> yu
    ( _, xv, EQ,  _) -> xv
    (xu,  _,  _, EQ) -> xu

    (GT,  _,  _, GT) -> GT
    ( _, GT, GT,  _) -> GT
    (LT,  _,  _, LT) -> LT
    ( _, LT, LT,  _) -> LT

    -- x > u > y, x > v > y
    (GT, GT, LT, LT)
      | u <= v    -> x `compare` Add (Nat (eval u - eval y)) v
      | otherwise -> x `compare` Add u (Nat (eval v - eval y))
    -- y > u > x, y > v > x
    (LT, LT, GT, GT)
      | u <= v    -> y `compare` Add (Nat (eval u - eval x)) v
      | otherwise -> y `compare` Add u (Nat (eval v - eval x))
    -- u > x > v, u > y > v
    (LT, GT, LT, GT)
      | x <= y    -> Add (Nat (eval x - eval v)) y `compare` u
      | otherwise -> Add x (Nat (eval y - eval v)) `compare` u
    -- v > x > u, v > y > u
    (GT, LT, GT, LT)
      | x <= y    -> Add (Nat (eval x - eval u)) y `compare` v
      | otherwise -> Add x (Nat (eval y - eval u)) `compare` v

compareMulMul :: Huge -> Huge -> Huge -> Huge -> Ordering
compareMulMul x y u v =
  case (x `compare` u, x `compare` v, y `compare` u, y `compare` v) of
    (EQ,  _,  _, yv) -> yv
    ( _, EQ, yu,  _) -> yu
    ( _, xv, EQ,  _) -> xv
    (xu,  _,  _, EQ) -> xu

    (GT,  _,  _, GT) -> GT
    ( _, GT, GT,  _) -> GT
    (LT,  _,  _, LT) -> LT
    ( _, LT, LT,  _) -> LT

    (GT, GT, LT, LT) -> uvSimpler
    (LT, LT, GT, GT) -> uvSimpler
    (LT, GT, LT, GT) -> xySimpler
    (GT, LT, GT, LT) -> xySimpler
  where
    uvSimpler = inverse $ compareNat (eval (Mul u v)) (Mul x y)
    xySimpler = compareNat (eval (Mul x y)) (Mul u v)

comparePowPow :: Huge -> Huge -> Huge -> Huge -> Ordering
comparePowPow x y u v = case (x `compare` u, y `compare` v) of
  (EQ, yv) -> yv
  (xu, EQ) -> xu
  (LT, LT) -> LT
  (GT, GT) -> GT
  (LT, GT) -> inverse $ compareNat (eval (Pow u v)) (Pow x y)
  (GT, LT) -> compareNat (eval (Pow x y)) (Pow u v)
