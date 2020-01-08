{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE ViewPatterns #-}

-- | Cantor pairing gives us an isomorphism between a single natural number and pairs of natural numbers. This package provides a modern API to this functionality using GHC generics, allowing the encoding of arbitrary combinations of finite or countably infinite types in natural number form.
--
-- As a user, all you need to do is derive generic and get the instances for free.
--
-- = Example
-- @
-- import GHC.Generics
-- import Cantor
--
-- data MyType = MyType {
--     value1 :: [ Maybe Bool ]
--   , value2 :: Integer
--   } deriving (Generic)
--
-- instance Cantor MyType
-- @
-- This should work nicely even with simple inductive types:
--
-- = Recursive example
-- @
-- data Tree a = Leaf | Branch (Tree a) a (Tree a) deriving (Generic)
--
-- instance Cantor a => Cantor (Tree a)
-- @
--
-- If your type is finite, you can specify this by deriving the @Finite@ typeclass, which is a subclass of @Cantor@:
--
-- = Finite example
-- @
-- data Color = Red | Green | Blue deriving (Generic)
--
-- instance Cantor Color
-- instance Finite Color
-- @
--

module Cantor
       ( cantorEnumeration
       , Cardinality(Countable)
       , pattern Finite
       , Cantor(..)
       , Finite
       , fCardinality
       ) where

import GHC.Generics
import GHC.Integer
import GHC.Int
import GHC.Word
import GHC.Natural
import Data.Semigroup
import Data.Functor.Identity
import qualified Data.Functor.Const
import Data.Proxy
import Math.NumberTheory.Powers.Squares (integerSquareRoot')
import Data.Void
import Data.Bits
import Data.Foldable (foldl')
import Math.NumberTheory.Logarithms

import qualified Data.Sequence
import qualified Data.Set
import qualified Data.IntSet

import Cantor.Huge

-- internal value-level representation, currently only used for function enumeration
data ESpace a = ESpace {
    eCardinality :: Cardinality
  , eToCantor :: Integer -> a
  , eFromCantor :: a -> Integer
  }

{-# INLINE defaultSpace #-}
defaultSpace :: forall a . Cantor a => ESpace a
defaultSpace = ESpace {
    eCardinality = cardinality @a
  , eToCantor = toCantor
  , eFromCantor = fromCantor
  }

{-# INLINE enumerateSpace #-}
enumerateSpace :: ESpace a -> [ a ]
enumerateSpace (ESpace c te _) = case c of
  Finite' 0 -> []
  Finite' i -> te <$> takeWhile (\k -> fromInteger k < i) [0..]
  Countable -> te <$> [ 0 .. ]

-- | Enumerates all values of a type by mapping @toCantor@ over the naturals or finite subset of naturals with the correct cardinality.
--
-- >>> take 5 cantorEnumeration :: [Data.IntSet.IntSet]
-- [fromList [],fromList [0],fromList [1],fromList [0,1],fromList [2]]
{-# INLINABLE cantorEnumeration #-}
cantorEnumeration :: Cantor a => [ a ]
cantorEnumeration = enumerateSpace defaultSpace

instance forall a b . (Finite a , Cantor b) => Cantor (a -> b) where
  {-# INLINE cardinality #-}
  cardinality = case (cardinality @a , cardinality @b) of
    (Finite' 0 , _) -> Finite' 1 -- anything to the zero power is one (including zero!)
    (Finite' c1 , Finite' c2) -> Finite' (c2 `pow` c1)
    _ -> Countable

  toCantor 0 _ = toCantor 0
  toCantor i a = toCantor $ cantorExp (fCardinality @a) (fromCantor a) i
    where
      cantorExp :: Integer -> Integer -> Integer -> Integer
      cantorExp 1 _ f = f
      cantorExp t x f = if x < b1
        then cantorExp b1 x $ fst (cantorSplit f)
        else cantorExp b2 (x - b1) $ snd (cantorSplit f)
        where
          (# t' , m' #) = divModInteger t 2
          !b1 = t' + m'
          b2 = t'

  fromCantor g = uncantorExp (fCardinality @a) (fromCantor . g . toCantor)
    where
      uncantorExp :: Integer -> (Integer -> Integer) -> Integer
      uncantorExp 1 f = f 0
      uncantorExp t f = cantorUnsplit (uncantorExp b1 f , uncantorExp b2 (\x -> f (x + b1)))
        where
          (# t' , m' #) = divModInteger t 2
          !b1 = t' + m'
          b2 = t'

instance (Finite a , Finite b) => Finite (a -> b)

-- | @Cardinality@ can be either @Finite@ or @Countable@. @Countable@ cardinality entails that a type has the same cardinality as the natural numbers. Note that not all infinite types are countable: for example, @Natural -> Natural@ is an infinite type, but it is not countably infinite; the basic intuition is that there is no possible way to enumerate all values of type @Natural -> Natural@ without "skipping" almost all of them. This is in contrast to the naturals, where despite their being infinite, we can trivially (by definition, in fact!) enumerate all of them without skipping any.
data Cardinality =
    Finite' Huge
  | Countable
  deriving (Generic,Eq,Ord,Show)

-- | Finite cardinality.
pattern Finite :: Integer -> Cardinality
pattern Finite n <- Finite' (evalWith (^) -> n)
  where
    Finite n = Finite' (fromInteger n)

{-# COMPLETE Finite, Countable #-}

-- | The @Finite@ typeclass simply entails that the @Cardinality@ of the set is finite.
class Cantor a => Finite a where
  {-# INLINE fCardinality' #-}
  fCardinality' :: Huge
  fCardinality' = case cardinality @a of
    Finite' i -> i
    _ -> error "Expected finite cardinality, got Countable."

-- | Cardinality of a finite type.
fCardinality :: forall a. Finite a => Integer
fCardinality = evalWith (^) (fCardinality' @a)

-- | The @Cantor@ class gives a way to convert a type to and from the natural numbers, as well as specifies the cardinality of the type.
class Cantor a where
  cardinality :: Cardinality

  {-# INLINE cardinality #-}
  default cardinality :: GCantor a (Rep a) => Cardinality
  cardinality = gCardinality' @a @(Rep a)

  {-# INLINABLE toCantor #-}
  toCantor :: Integer -> a -- ideally this should be `Fin n -> a` (for finite types)
                           -- or `N` (for countably infinite types).
                           -- I chose not to use `Natural` from `GHC.Natural`
                           -- because it's turned out to be a huge pain and integrates
                           -- poorly with the haskell ecosystem
  default toCantor :: (Generic a , GCantor a (Rep a)) => Integer -> a
  toCantor = to . gToCantor' @a @(Rep a)

  {-# INLINABLE fromCantor #-}
  fromCantor :: a -> Integer
  default fromCantor :: (Generic a , GCantor a (Rep a)) => a -> Integer
  fromCantor = gFromCantor' @a @(Rep a) . from


instance Cantor Natural where
  {-# INLINE cardinality #-}
  cardinality = Countable
  {-# INLINE toCantor #-}
  toCantor = fromInteger
  {-# INLINE fromCantor #-}
  fromCantor = toInteger

data IntAlg = Zero | Neg Natural | Pos Natural deriving (Generic,Show)

instance Cantor IntAlg

toIntAlg :: Integer -> IntAlg
toIntAlg 0 = Zero
toIntAlg x = if x < 0
  then Neg $ fromInteger $ negate (x + 1)
  else Pos $ fromInteger $ x - 1

fromIntAlg :: IntAlg -> Integer
fromIntAlg Zero = 0
fromIntAlg (Neg x) = negate (toInteger x) - 1
fromIntAlg (Pos x) = toInteger x + 1

instance Cantor Integer where
  {-# INLINE cardinality #-}
  cardinality = Countable

  toCantor = fromIntAlg . toCantor

  fromCantor = fromCantor . toIntAlg

instance Cantor () where
instance Finite ()

instance Cantor Void
instance Finite Void

instance Finite Bool
instance Cantor Bool where
  {-# INLINE cardinality #-}
  cardinality = Finite' 2

  {-# INLINE toCantor #-}
  toCantor 0 = False
  toCantor _ = True

  {-# INLINE fromCantor #-}
  fromCantor False = 0
  fromCantor _ = 1


instance Finite Int8
instance Cantor Int8 where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (8 :: Integer)
  {-# INLINE toCantor #-}
  toCantor = fromInteger . toCantor @Integer
  {-# INLINE fromCantor #-}
  fromCantor = fromCantor @Integer . toInteger

instance Finite Int16
instance Cantor Int16 where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (16 :: Integer)
  {-# INLINE toCantor #-}
  toCantor = fromInteger . toCantor @Integer
  {-# INLINE fromCantor #-}
  fromCantor = fromCantor @Integer . toInteger

instance Finite Int32
instance Cantor Int32 where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (32 :: Integer)
  {-# INLINE toCantor #-}
  toCantor = fromInteger . toCantor @Integer
  {-# INLINE fromCantor #-}
  fromCantor = fromCantor @Integer . toInteger

instance Finite Int64
instance Cantor Int64 where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (64 :: Integer)
  {-# INLINE toCantor #-}
  toCantor = fromInteger . toCantor @Integer
  {-# INLINE fromCantor #-}
  fromCantor = fromCantor @Integer . toInteger

instance Finite Int
instance Cantor Int where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (finiteBitSize @Int undefined)
  {-# INLINE toCantor #-}
  toCantor = fromInteger . toCantor @Integer
  {-# INLINE fromCantor #-}
  fromCantor = fromCantor @Integer . toInteger

instance Finite Word8
instance Cantor Word8 where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (8 :: Integer)
  {-# INLINE toCantor #-}
  toCantor = fromIntegral
  {-# INLINE fromCantor #-}
  fromCantor = fromIntegral

instance Finite Word16
instance Cantor Word16 where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (16 :: Integer)
  {-# INLINE toCantor #-}
  toCantor = fromIntegral
  {-# INLINE fromCantor #-}
  fromCantor = fromIntegral

instance Finite Word32
instance Cantor Word32 where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (32 :: Integer)
  {-# INLINE toCantor #-}
  toCantor = fromIntegral
  {-# INLINE fromCantor #-}
  fromCantor = fromIntegral

instance Finite Word64
instance Cantor Word64 where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (64 :: Integer)
  {-# INLINE toCantor #-}
  toCantor = fromIntegral
  {-# INLINE fromCantor #-}
  fromCantor = fromIntegral

instance Finite Word
instance Cantor Word where
  {-# INLINE cardinality #-}
  cardinality = Finite' $ 2 ^ (finiteBitSize @Word undefined)
  {-# INLINE toCantor #-}
  toCantor = fromIntegral
  {-# INLINE fromCantor #-}
  fromCantor =  fromIntegral

instance Finite Char
instance Cantor Char where
  {-# INLINE cardinality #-}
  cardinality = Finite' . fromIntegral $ (fromEnum (maxBound :: Char) :: Int) + 1
  {-# INLINE toCantor #-}
  toCantor x = toEnum (fromIntegral x :: Int)
  {-# INLINE fromCantor #-}
  fromCantor x = fromIntegral (fromEnum x :: Int)

instance (Cantor a , Cantor b) => Cantor (a , b)
instance (Cantor a , Cantor b , Cantor c) => Cantor (a , b , c)
instance (Cantor a , Cantor b , Cantor c , Cantor d) => Cantor (a , b , c , d)
instance (Cantor a , Cantor b , Cantor c , Cantor d , Cantor e) => Cantor (a , b , c , d , e)
instance (Cantor a , Cantor b , Cantor c , Cantor d , Cantor e , Cantor f) => Cantor (a , b , c , d , e , f)
instance (Cantor a , Cantor b , Cantor c , Cantor d , Cantor e , Cantor f , Cantor g) => Cantor (a , b , c , d , e , f , g)

instance Cantor a => Cantor (Product a)
instance Cantor a => Cantor (Sum a)
instance Cantor a => Cantor (Last a)
instance Cantor a => Cantor (First a)
instance Cantor a => Cantor (Identity a)
instance Cantor a => Cantor (Data.Functor.Const.Const a b)
instance Cantor a => Cantor (Option a)
instance Cantor a => Cantor (Min a)
instance Cantor a => Cantor (Max a)
instance Cantor (Proxy a)
instance (Cantor a , Cantor b) => Cantor (Arg a b)

instance Cantor a => Cantor (Maybe a)
instance (Cantor a , Cantor b) => Cantor (Either a b)

instance (Finite a , Finite b) => Finite (a , b)
instance (Finite a , Finite b , Finite c) => Finite (a , b , c)
instance (Finite a , Finite b , Finite c , Finite d) => Finite (a , b , c , d)
instance (Finite a , Finite b , Finite c , Finite d , Finite e) => Finite (a , b , c , d , e)
instance (Finite a , Finite b , Finite c , Finite d , Finite e , Finite f) => Finite (a , b , c , d , e , f)
instance (Finite a , Finite b , Finite c , Finite d , Finite e , Finite f , Finite g) => Finite (a , b , c , d , e , f , g)

instance Finite a => Finite (Product a)
instance Finite a => Finite (Sum a)
instance Finite a => Finite (Last a)
instance Finite a => Finite (First a)
instance Finite a => Finite (Identity a)
instance Finite a => Finite (Data.Functor.Const.Const a b)
instance Finite a => Finite (Option a)
instance Finite a => Finite (Min a)
instance Finite a => Finite (Max a)
instance Finite (Proxy a)
instance (Finite a , Finite b) => Finite (Arg a b)

instance Finite a => Finite (Maybe a)
instance (Finite a , Finite b) => Finite (Either a b)

instance Cantor a => Cantor [ a ]
instance Cantor a => Cantor (Data.Sequence.Seq a) where
  {-# INLINE cardinality #-}
  cardinality = cardinality @[ a ]
  toCantor = Data.Sequence.fromList . toCantor
  fromCantor = fromCantor . foldr (:) []

-- this algorithm is correct, but too slow for large a
-- instance (Ord a , Finite a , Cantor b) => Cantor (M.Map a b) where
--   cardinality = cardinality @(a -> Maybe b)
--   toCantor i = m
--     where
--       m :: M.Map a b
--       m = M.fromList $ mapMaybe (\(a,w) -> (,) a <$> w) $ zip (toCantor <$> [ 0 .. ]) (eToCantor es i)

--       es :: ESpace [ Maybe b ]
--       es = nary (fCardinality @a) defaultSpace

--   fromCantor g = eFromCantor es . fmap (\i -> M.lookup (toCantor i) g) $ [ 0 .. (fCardinality @a - 1) ]
--     where
--       es :: ESpace [ Maybe b ]
--       es = nary (fCardinality @a) defaultSpace

-- instance (Ord a , Finite a , Finite b) => Finite (M.Map a b)

-- espace for `Set (Fin c)`
fSetEnum :: Huge -> ESpace (Data.Set.Set Integer)
fSetEnum c = ESpace (Finite' (2 `pow` c)) t f
  where
    t :: Integer -> Data.Set.Set Integer
    t 0 = Data.Set.empty
    t m = Data.Set.fromAscList $ foldr g mempty [ 0 .. (integerLog2 m + 1) ]
      where
        g :: Int -> [ Integer ] -> [ Integer ]
        g i s = if testBit m i
          then toInteger i : s
          else s

    f :: Data.Set.Set Integer -> Integer
    f = foldl' g 0
      where
        g :: Integer -> Integer -> Integer
        g a i = setBit a (fromInteger i)

instance (Ord a , Finite a) => Cantor (Data.Set.Set a) where
  {-# INLINE cardinality #-}
  cardinality = Finite' (2 `pow` fCardinality' @a)
  -- would be nice to map monotonic and save a log here, but that only works when
  -- Ord a respects the ordering on Integer, which we have no assurance of
  toCantor = Data.Set.map toCantor . eToCantor (fSetEnum (fCardinality' @a))
  fromCantor = eFromCantor (fSetEnum (fCardinality' @a)) . Data.Set.map fromCantor

instance (Ord a , Finite a) => Finite (Data.Set.Set a)

-- espace for `IntSet (Fin c)`, where c is in proper range
fSetEnum' :: Huge -> ESpace Data.IntSet.IntSet
fSetEnum' c = ESpace (Finite' (2 `pow` c)) t f
  where
    t :: Integer -> Data.IntSet.IntSet
    t 0 = Data.IntSet.empty
    t m = Data.IntSet.fromAscList $ foldr g mempty [ 0 .. (integerLog2 m + 1) ]
      where
        g :: Int -> [ Int ] -> [ Int ]
        g i s = if testBit m i
          then i : s
          else s

    f :: Data.IntSet.IntSet -> Integer
    f = Data.IntSet.foldl' g 0
      where
        g :: Integer -> Int -> Integer
        g a i = setBit a i

instance Cantor Data.IntSet.IntSet where
  {-# INLINE cardinality #-}
  cardinality = Finite' (2 `pow` fCardinality' @Int)
  toCantor = eToCantor (fSetEnum' (fCardinality' @Int))
  fromCantor = eFromCantor (fSetEnum' (fCardinality' @Int))

instance Finite Data.IntSet.IntSet

-- this algorithm is wrong; only works on Countable a.
-- instance Cantor a => Cantor (Data.IntMap.Lazy.IntMap a) where
--   cardinality = case cardinality @a of
--     Countable -> Countable
--     Finite c -> Finite $ (c + 1) ^ fCardinality @Int
--   toCantor i = if i == 0 then mempty else case cantorSplit i of
--     (j , k) -> Data.IntMap.Lazy.fromAscList $ zip (Data.IntSet.toAscList s) as
--       where
--         s :: Data.IntSet.IntSet
--         s = toCantor (j + 1)

--         es :: ESpace [ a ]
--         es = nary (toInteger (Data.IntSet.size s)) defaultSpace

--         as :: [ a ]
--         as = eToCantor es k
--   fromCantor m = if Data.IntMap.Lazy.null m then 0 else case unzip (Data.IntMap.Lazy.toAscList m) of
--     (is , as) -> cantorUnsplit (fromCantor s , eFromCantor es as)
--       where
--         s = Data.IntSet.fromAscList is

--         es :: ESpace [ a ]
--         es = nary (toInteger (Data.IntSet.size s)) defaultSpace

-- instance Finite a => Finite (Data.IntMap.Lazy.IntMap a)


-- https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function
-- adapted for integer square rooting in the w, which should yield the same result
-- but benchmarks significantly faster. buuut on closer inspection that makes no sense, since
-- this is exactly what arithmoi is doing anyway...
--
-- also, maybe try this https://gist.github.com/orlp/3481770
cantorSplit :: Integer -> (Integer , Integer)
cantorSplit i =
  let -- original implementation (convert to/from float for the sqrt)
      -- w :: Int = floor (0.5 * (sqrt (8 * fromIntegral i + 1 :: Double) - 1))
      t = (w^(2 :: Int) + w) `quot` 2
      y = i - t
      x = w - y
  in
  (x , y)
  where
    w = (integerSquareRoot' (8 * i + 1) - 1) `div` 2

cantorUnsplit :: (Integer , Integer) -> Integer
cantorUnsplit (x , y) = (((x + y + 1) * (x + y)) `quot` 2) + y

class GCantor s f where
  hasExit :: Bool
  gCardinality' :: Cardinality
  gToCantor' :: Integer -> f a
  gFromCantor' :: f a -> Integer

instance GCantor s V1 where
  {-# INLINE hasExit #-}
  hasExit = False
  {-# INLINE gCardinality' #-}
  gCardinality' = Finite' 0
  gToCantor' = undefined
  gFromCantor' = undefined

instance GCantor s U1 where
  {-# INLINE hasExit #-}
  hasExit = True
  {-# INLINE gCardinality' #-}
  gCardinality' = Finite' 1
  {-# INLINE gToCantor' #-}
  gToCantor' _ = U1
  {-# INLINE gFromCantor' #-}
  gFromCantor' _ = 0

instance {-# OVERLAPPING #-} Cantor a => GCantor a (K1 i a) where
  {-# INLINE hasExit #-}
  hasExit = False
  {-# INLINE gCardinality' #-}
  gCardinality' = Countable
  {-# INLINE gToCantor' #-}
  gToCantor' = K1 . toCantor
  {-# INLINE gFromCantor' #-}
  gFromCantor' (K1 x) = fromCantor x

instance {-# OVERLAPPABLE #-} Cantor b => GCantor w (K1 i b) where
  {-# INLINE hasExit #-}
  hasExit = True
  {-# INLINE gCardinality' #-}
  gCardinality' = cardinality @b
  {-# INLINE gToCantor' #-}
  gToCantor' = K1 . toCantor
  {-# INLINE gFromCantor' #-}
  gFromCantor' (K1 x) = fromCantor x

instance (GCantor s a , GCantor s b) => GCantor s (a :*: b) where
  {-# INLINE hasExit #-}
  hasExit = hasExit @s @a && hasExit @s @b
  {-# INLINE gCardinality' #-}
  gCardinality' = case (gCardinality' @s @a , gCardinality' @s @b) of
    (Finite' i , Finite' j) -> Finite' (i * j)
    (Finite' 0 , _) -> Finite' 0
    (_ , Finite' 0) -> Finite' 0
    _ -> Countable

  {-# INLINABLE gToCantor' #-}
  gToCantor' i = case (gCardinality' @s @a , gCardinality' @s @b) of
    (Finite ca, Finite cb) ->
      let par_s = min ca cb -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      -- optimisation - if tri_l is 0, one or both of these is trivial and we have a line
      if i < tri_a
         then -- we're in the triangle, so just use cantor
              case cantorSplit i of
                (a , b) -> (gToCantor' @s @a a :*: gToCantor' @s @b b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
                  par_l = max ca cb - tri_l
                  par_a = par_s * par_l in
              if j < par_a
                 then -- find their coordinates in the box
                      -- and then skew them to the real grid
                      case divModInteger j par_s of
                        (# l , s #) ->
                          let c1 = (l + tri_l) - s
                              c2 = s
                              (a , b) = if ca <= cb
                                          then (c2 , c1)
                                          else (c1 , c2)
                          in
                          (gToCantor' @s @a a :*: gToCantor' @s @b b)
                 else let k = j - par_a
                          l = tri_a - (k + 1) in
                      case cantorSplit l of
                        (a , b) -> (gToCantor' @s @a (ca - (a + 1)) :*: gToCantor' @s @b (cb - (b + 1)))
    (Finite ca, Countable) ->
      let par_s = ca -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      if i < tri_a
         then case cantorSplit i of
                (a , b) -> (gToCantor' @s @a a :*: gToCantor' @s @b b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
              in
              case divModInteger j par_s of
                (# l , s #) ->
                  let c1 = (l + tri_l) - s
                      c2 = s
                      (a , b) = (c2 , c1)
                  in
                  (gToCantor' @s @a a :*: gToCantor' @s @b b)

    (Countable , Finite cb) ->
      let par_s = cb -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      if i < tri_a
         then case cantorSplit i of
                (a , b) -> (gToCantor' @s @a a :*: gToCantor' @s @b b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
              in
              case divModInteger j par_s of
                (# l , s #) ->
                  let c1 = (l + tri_l) - s
                      c2 = s
                      (a , b) = (c1 , c2)
                  in
                  (gToCantor' @s @a a :*: gToCantor' @s @b b)
    _ -> case cantorSplit i of
      (a , b) -> (gToCantor' @s @a a :*: gToCantor' @s @b b)

  {-# INLINABLE gFromCantor' #-}
  gFromCantor' (a :*: b) = case (gCardinality' @s @a , gCardinality' @s @b) of
    (Finite ca, Finite cb) ->
      let (x , y) = (gFromCantor' @s @a a , gFromCantor' @s @b b)
          par_s = min ca cb
          tri_l = par_s - 1
      in
      if y < tri_l - x
         then cantorUnsplit $ (x , y)
         else let x'' = ca - (x + 1)
                  y'' = cb - (y + 1)
              in
              if y'' < tri_l - x''
                 then (ca * cb) - (cantorUnsplit (x'' , y'') + 1)
                 else let (x' , y') = if ca <= cb
                                         then (x , y - (tri_l - x))
                                         else (y , x - (tri_l - y))
                          tri_a = (tri_l * (tri_l + 1)) `div` 2
                      in
                      tri_a + x' + y' * par_s
    (Finite ca, Countable) ->
      let (x , y) = (gFromCantor' @s @a a , gFromCantor' @s @b b)
          par_s = ca
          tri_l = par_s - 1
      in
      if y < tri_l - x
         then cantorUnsplit $ (x , y)
         else let (x' , y') = (x , y - (tri_l - x))
                  tri_a = (tri_l * (tri_l + 1)) `div` 2
              in
              tri_a + x' + y' * par_s
    (Countable, Finite cb) ->
      let (x , y) = (gFromCantor' @s @a a , gFromCantor' @s @b b)
          par_s = cb
          tri_l = par_s - 1
      in
      if y < tri_l - x
         then cantorUnsplit $ (x , y)
         else let (x' , y') = (y , x - (tri_l - y))
                  tri_a = (tri_l * (tri_l + 1)) `div` 2
              in
              tri_a + x' + y' * par_s
    _ -> cantorUnsplit (gFromCantor' @s @a a , gFromCantor' @s @b b)


-- in this instance, make sure we head towards the exit if there is one, otherwise we can get
-- stuck endlessly in the labyrinth
instance (GCantor s a , GCantor s b) => GCantor s (a :+: b) where
  {-# INLINE hasExit #-}
  hasExit = hasExit @s @a || hasExit @s @b
  {-# INLINE gCardinality' #-}
  gCardinality' = case (gCardinality' @s @a , gCardinality' @s @b) of
    (Finite' i , Finite' j) -> Finite' (i + j)
    _ -> Countable

  {-# INLINABLE gToCantor' #-}
  gToCantor' i = case (gCardinality' @s @a , gCardinality' @s @b) of
    (Finite ca, Finite cb) -> if i < 2 * min ca cb
      then case divModInteger i 2 of
        (# k , 0 #) -> L1 $ gToCantor' @s @a k
        (# k , _ #) -> R1 $ gToCantor' @s @b k
      else if ca > cb
           then L1 $ gToCantor' @s @a (i - cb)
           else R1 $ gToCantor' @s @b (i - ca)
    (Finite ca, Countable) -> if i < 2 * ca
      then case divModInteger i 2 of
        (# k , 0 #) -> L1 $ gToCantor' @s @a k
        (# k , _ #) -> R1 $ gToCantor' @s @b k
      else R1 $ gToCantor' @s @b (i - ca)
    (Countable , Finite{}) -> case gToCantor' @s @(b :+: a) i of
      L1 x -> R1 x
      R1 x -> L1 x
    _ -> if not (hasExit @s @a) && hasExit @s @b
            then case gToCantor' @s @(b :+: a) i of
              L1 x -> R1 x
              R1 x -> L1 x
            else case divModInteger i 2 of
             (# k , 0 #) -> L1 $ gToCantor' @s @a k
             (# k , _ #) -> R1 $ gToCantor' @s @b k

  {-# INLINABLE gFromCantor' #-}
  gFromCantor' (L1 x) = case gCardinality' @s @b of
    Finite' cb -> case gCardinality' @s @a of
      Countable -> gFromCantor' @s @(b :+: a) $ R1 x
      _ -> case gFromCantor' @s @a x of
        0 -> 0
        i -> i + evalWith (^) (min cb (fromInteger i))
    Countable -> case gCardinality' @s @a of
      Countable -> if not (hasExit @s @a) && hasExit @s @b
        then gFromCantor' @s @(b :+: a) $ R1 x
        else case gFromCantor' @s @a x of
          0 -> 0
          i -> 2 * i
      _ -> case gFromCantor' @s @a x of
        0 -> 0
        i -> 2 * i
  gFromCantor' (R1 x) = case gCardinality' @s @a of
    Finite' ca -> case gFromCantor' @s @b x of
      0 -> 1
      i -> i + evalWith (^) (min ca (fromInteger (i + 1)))
    Countable -> case gCardinality' @s @b of
      Finite{}  -> gFromCantor' @s @(b :+: a) $ L1 x
      Countable -> if not (hasExit @s @a) && hasExit @s @b
        then gFromCantor' @s @(b :+: a) $ L1 x
        else case gFromCantor' @s @b x of
          0 -> 1
          i -> 2 * i + 1

instance GCantor s f => GCantor s (M1 i t f) where
  {-# INLINE hasExit #-}
  hasExit = hasExit @s @f

  {-# INLINE gCardinality' #-}
  gCardinality' = gCardinality' @s @f

  {-# INLINE gToCantor' #-}
  gToCantor' = M1 . gToCantor' @s @f

  {-# INLINE gFromCantor' #-}
  gFromCantor' (M1 x) = gFromCantor' @s @f x
