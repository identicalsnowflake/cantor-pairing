{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}

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
       , Cardinality(..)
       , Cantor(..)
       , Finite(..)
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
import Data.Bits (finiteBitSize)
import Data.Kind
import qualified Data.Map as M


-- internal value-level representation, currently only used for function enumeration
data ESpace a = ESpace {
    eCardinality :: Cardinality
  , eToCantor :: Integer -> a
  , eFromCantor :: a -> Integer
  }

defaultSpace :: forall a . Cantor a => ESpace a
defaultSpace = ESpace {
    eCardinality = cardinality @a
  , eToCantor = toCantor
  , eFromCantor = fromCantor
  }

enumerateSpace :: ESpace a -> [ a ]
enumerateSpace (ESpace c te _) = case c of
  Finite 0 -> []
  Finite i -> te <$> [ 0 .. (i - 1) ]
  Countable -> te <$> [ 0 .. ]

-- | Enumerates all values of a type by mapping @toCantor@ over the naturals.
cantorEnumeration :: Cantor a => [ a ]
cantorEnumeration = enumerateSpace defaultSpace

instance forall a b . (Finite a , Cantor b) => Cantor (a -> b) where
  cardinality = case (cardinality @a , cardinality @b) of
    (Finite 0 , _) -> Finite 1 -- anything to the zero power is one (including zero!)
    (Finite c1 , Finite c2) -> Finite (c2 ^ c1)
    _ -> Countable

  toCantor i a = m M.! fromCantor a
    where
      m :: M.Map Integer b
      m = M.fromList $ zip [ 0 .. ] (eToCantor es i)
      
      es :: ESpace [ b ]
      es = nary (fCardinality @a) defaultSpace

  fromCantor g = eFromCantor es . fmap ((M.!) m) $ [ 0 .. (fCardinality @a - 1) ]
    where
      es :: ESpace [ b ]
      es = nary (fCardinality @a) defaultSpace
      
      m :: M.Map Integer b
      m = M.fromList $ (\x -> (fromCantor x , g x)) <$> enumerateSpace (defaultSpace @a)

instance (Finite a , Finite b) => Finite (a -> b)

-- | @Cardinality@ can be either @Finite@ or @Countable@. @Countable@ cardinality entails that a type has the same cardinality as the natural numbers. Note that not all infinite types are countable: for example, @Natural -> Natural@ is an infinite type, but it is not countably infinite; the basic intuition is that there is no possible way to enumerate all values of type @Natural -> Natural@ without "skipping" almost all of them. This is in contrast to the naturals, where despite their being infinite, we can trivially (by definition, in fact!) enumerate all of them without skipping any.
data Cardinality =
    Finite Integer
  | Countable
  deriving (Generic,Eq,Ord,Show)

-- | The @Finite@ typeclass simply entails that the @Cardinality@ of the set is finite.
class Cantor a => Finite a where
  fCardinality :: Integer
  fCardinality = case cardinality @a of
    Finite i -> i
    _ -> error "Expected finite cardinality, got Countable."

-- | The @Cantor@ class gives a way to convert a type to and from the natural numbers, as well as specifies the cardinality of the type.
class Cantor a where
  cardinality :: Cardinality
  
  default cardinality :: GCantor' (ToStruct a (Rep a)) (Rep a) => Cardinality
  cardinality = gCardinality' @(ToStruct a (Rep a)) @(Rep a)
  
  toCantor :: Integer -> a -- ideally this should be `Fin n -> a` (for finite types)
                           -- or `N` (for countably infinite types).
                           -- I chose not to use `Natural` from `GHC.Natural`
                           -- because it's turned out to be a huge pain and integrates
                           -- poorly with the haskell ecosystem
  default toCantor :: (Generic a , GCantor' (ToStruct a (Rep a)) (Rep a)) => Integer -> a
  toCantor = to . gToCantor' @(ToStruct a (Rep a)) @(Rep a)

  fromCantor :: a -> Integer
  default fromCantor :: (Generic a , GCantor' (ToStruct a (Rep a)) (Rep a)) => a -> Integer
  fromCantor = gFromCantor' @(ToStruct a (Rep a)) @(Rep a) . from
  

instance Cantor Natural where
  cardinality = Countable
  toCantor = fromInteger
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
  cardinality = Countable
  
  toCantor = fromIntAlg . toCantor
  
  fromCantor = fromCantor . toIntAlg

instance Finite ()
instance Cantor ()

instance Cantor Void
instance Finite Void

instance Finite Bool
instance Cantor Bool where
  cardinality = Finite 2

  toCantor 0 = False
  toCantor _ = True
  
  fromCantor False = 0
  fromCantor _ = 1


instance Finite Int8
instance Cantor Int8 where
  cardinality = Finite $ 2 ^ (8 :: Integer)
  toCantor = fromInteger . toCantor @Integer
  fromCantor = fromCantor @Integer . toInteger

instance Finite Int16
instance Cantor Int16 where
  cardinality = Finite $ 2 ^ (16 :: Integer)
  toCantor = fromInteger . toCantor @Integer
  fromCantor = fromCantor @Integer . toInteger

instance Finite Int32
instance Cantor Int32 where
  cardinality = Finite $ 2 ^ (32 :: Integer)
  toCantor = fromInteger . toCantor @Integer
  fromCantor = fromCantor @Integer . toInteger

instance Finite Int64
instance Cantor Int64 where
  cardinality = Finite $ 2 ^ (64 :: Integer)
  toCantor = fromInteger . toCantor @Integer
  fromCantor = fromCantor @Integer . toInteger

instance Finite Int
instance Cantor Int where
  cardinality = Finite $ 2 ^ (finiteBitSize @Int undefined)
  toCantor = fromInteger . toCantor @Integer
  fromCantor = fromCantor @Integer . toInteger

instance Finite Word8
instance Cantor Word8 where
  cardinality = Finite $ 2 ^ (8 :: Integer)
  toCantor = fromIntegral
  fromCantor = fromIntegral

instance Finite Word16
instance Cantor Word16 where
  cardinality = Finite $ 2 ^ (16 :: Integer)
  toCantor = fromIntegral
  fromCantor = fromIntegral

instance Finite Word32
instance Cantor Word32 where
  cardinality = Finite $ 2 ^ (32 :: Integer)
  toCantor = fromIntegral
  fromCantor = fromIntegral

instance Finite Word64
instance Cantor Word64 where
  cardinality = Finite $ 2 ^ (64 :: Integer)
  toCantor = fromIntegral
  fromCantor = fromIntegral

instance Finite Word
instance Cantor Word where
  cardinality = Finite $ 2 ^ (finiteBitSize @Word undefined)
  toCantor = fromIntegral 
  fromCantor =  fromIntegral

instance Finite Char
instance Cantor Char where
  cardinality = Finite . fromIntegral $ (fromEnum (maxBound :: Char) :: Int) + 1
  toCantor x = toEnum (fromIntegral x :: Int)
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


-- ES is just an alias to get in a position to use stimes for nary to get the nice algorithm
data ES a = ES !Int (ESpace (Endo [ a ])) (ESpace [ a ])

instance Semigroup (ES a) where
  (<>) (ES a x x') (ES b y y') = ES (a + b) s1 s2
    where
      s1 :: ESpace (Endo [ a ])
      s1 = case x ***  y of
        (ESpace c f _) -> ESpace c f' undefined
          where
            f' :: Integer -> Endo [ a ]
            f' i = case f i of
             (xs , ys) -> xs <> ys

      s2 :: ESpace [ a ]
      s2 = case x' *** y' of
        (ESpace c _ t) -> ESpace c undefined t'
          where
            t' :: [ a ] -> Integer
            t' = t . splitAt a

nary :: forall a . Integer -> ESpace a -> ESpace [ a ]
nary 0 _ = undefined
nary i (ESpace c f t) = case stimes i es' of
  (ES _ (ESpace c' f' _) (ESpace _ _ t')) -> ESpace c' (flip appEndo [] . f') t'
  where
    toE :: [ a ] -> Endo [ a ]
    toE = Endo . (<>)
    
    es' :: ES a
    es' = ES 1 (ESpace c (\j -> toE [ f j ]) undefined) $ ESpace c undefined $ \case
      [ x ] -> t x
      _ -> error "Bounds error."


infixr 7 ***
(***) :: forall a b . ESpace a -> ESpace b -> ESpace (a , b)
(***) (ESpace (Finite ca) tea fea) (ESpace (Finite cb) teb feb) =
  ESpace (Finite (ca * cb)) tec fec
  where
    tec i =
      let par_s = min ca cb -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      -- optimisation - if tri_l is 0, one or both of these is trivial and we have a line
      if i < tri_a
         then -- we're in the triangle, so just use cantor
              case cantorSplit i of
                (a , b) -> (tea a , teb b)
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
                          (tea a , teb b)
                 else let k = j - par_a
                          l = tri_a - (k + 1) in
                      case cantorSplit l of
                        (a , b) -> (tea (ca - (a + 1)) , teb (cb - (b + 1)))

    fec (a , b) =
      let (x , y) = (fea a , feb b)
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
(***) (ESpace (Finite ca) tea fea) (ESpace Countable teb feb) =
  ESpace (if ca == 0 then Finite 0 else Countable) tec fec
  where
    tec i =
      let par_s = ca -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      if i < tri_a
         then case cantorSplit i of
                (a , b) -> (tea a , teb b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
              in
              case divModInteger j par_s of
                (# l , s #) ->
                  let c1 = (l + tri_l) - s
                      c2 = s
                      (a , b) = (c2 , c1)
                  in
                  (tea a , teb b)

    fec (a , b) =
      let (x , y) = (fea a , feb b)
          par_s = ca
          tri_l = par_s - 1
      in
      if y < tri_l - x
         then cantorUnsplit $ (x , y)
         else let (x' , y') = (x , y - (tri_l - x))
                  tri_a = (tri_l * (tri_l + 1)) `div` 2
              in
              tri_a + x' + y' * par_s
(***) (ESpace Countable tea fea) (ESpace (Finite cb) teb feb) =
  ESpace (if cb == 0 then Finite 0 else Countable) tec fec
  where
    tec i =
      let par_s = cb -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      if i < tri_a
         then case cantorSplit i of
                (a , b) -> (tea a , teb b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
              in
              case divModInteger j par_s of
                (# l , s #) ->
                  let c1 = (l + tri_l) - s
                      c2 = s
                      (a , b) = (c1 , c2)
                  in
                  (tea a , teb b)

    fec (a , b) =
      let (x , y) = (fea a , feb b)
          par_s = cb
          tri_l = par_s - 1
      in
      if y < tri_l - x
         then cantorUnsplit $ (x , y)
         else let (x' , y') = (y , x - (tri_l - y))
                  tri_a = (tri_l * (tri_l + 1)) `div` 2
              in
              tri_a + x' + y' * par_s
(***) (ESpace _ tea fea) (ESpace _ teb feb) =
  ESpace Countable tec fec
  where
    tec i = case cantorSplit i of
      (a , b) -> (tea a , teb b)

    fec (a , b) = cantorUnsplit (fea a , feb b)


-- https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function
-- adapted for integer square rooting in the w, which should yield the same result
-- but benchmarks significantly faster. buuut on closer inspection that makes no sense, since
-- this is exactly what arithmoi is doing anyway...
--
-- also, maybe try this https://gist.github.com/orlp/3481770
cantorSplit :: Integer -> (Integer , Integer)
cantorSplit i = 
  let w = (integerSquareRoot' (8 * i + 1) - 1) `div` 2 
      -- original implementation (convert to/from float for the sqrt)
      -- w :: Int = floor (0.5 * (sqrt (8 * fromIntegral i + 1 :: Double) - 1))
      t = (w^(2 :: Int) + w) `quot` 2
      y = i - t
      x = w - y
  in
  (x , y)

cantorUnsplit :: (Integer , Integer) -> Integer
cantorUnsplit (x , y) = (((x + y + 1) * (x + y)) `quot` 2) + y

-- thanks /u/yumiova for proposing this approach!
data Struct
    = Void
    | Unit
    | Const Type -- Reflects K1 cases that are *maybe not recursive*
    | Recur Type -- Reflects K1 cases that are *definitively recursive*
    | Struct :+ Struct
    | Struct :* Struct

type family ToStruct b i where
    ToStruct b V1 = 'Void
    ToStruct b U1 = 'Unit
    ToStruct b (K1 i b) = 'Recur b -- If the constant node equals the
                                   -- recursive case, mark as recursive
    ToStruct b (K1 i a) = 'Const a
    ToStruct b (M1 i c f) = ToStruct b f
    ToStruct b (f :+: g) = ToStruct b f ':+ ToStruct b g
    ToStruct b (f :*: g) = ToStruct b f ':* ToStruct b g

class GCantor' (s :: Struct) f where
  hasExit :: Bool
  gCardinality' :: Cardinality
  gToCantor' :: Integer -> f a
  gFromCantor' :: f a -> Integer

instance GCantor' 'Void V1 where
  hasExit = False
  gCardinality' = Finite 0
  gToCantor' = undefined
  gFromCantor' = undefined

instance GCantor' 'Unit U1 where
  hasExit = True
  gCardinality' = Finite 1
  gToCantor' _ = U1
  gFromCantor' _ = 0

instance {-# OVERLAPPING #-} Cantor a => GCantor' ('Recur a) (K1 i a) where
  hasExit = False
  gCardinality' = Countable
  gToCantor' = K1 . toCantor
  gFromCantor' (K1 x) = fromCantor x

instance Cantor b => GCantor' w (K1 i b) where
  hasExit = True
  gCardinality' = cardinality @b
  gToCantor' = K1 . toCantor
  gFromCantor' (K1 x) = fromCantor x

instance (GCantor' s a , GCantor' t b) => GCantor' (s ':* t) (a :*: b) where
  hasExit = hasExit @s @a && hasExit @t @b
  gCardinality' = case (gCardinality' @s @a , gCardinality' @t @b) of
    (Finite i , Finite j) -> Finite (i * j)
    (Finite 0 , _) -> Finite 0
    (_ , Finite 0) -> Finite 0
    _ -> Countable

  gToCantor' i = case (gCardinality' @s @a , gCardinality' @t @b) of
    (Finite ca , Finite cb) ->
      let par_s = min ca cb -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      -- optimisation - if tri_l is 0, one or both of these is trivial and we have a line
      if i < tri_a
         then -- we're in the triangle, so just use cantor
              case cantorSplit i of
                (a , b) -> (gToCantor' @s @a a :*: gToCantor' @t @b b)
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
                          (gToCantor' @s @a a :*: gToCantor' @t @b b)
                 else let k = j - par_a
                          l = tri_a - (k + 1) in
                      case cantorSplit l of
                        (a , b) -> (gToCantor' @s @a (ca - (a + 1)) :*: gToCantor' @t @b (cb - (b + 1)))
    (Finite ca , Countable) ->
      let par_s = ca -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      if i < tri_a
         then case cantorSplit i of
                (a , b) -> (gToCantor' @s @a a :*: gToCantor' @t @b b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
              in
              case divModInteger j par_s of
                (# l , s #) ->
                  let c1 = (l + tri_l) - s
                      c2 = s
                      (a , b) = (c2 , c1)
                  in
                  (gToCantor' @s @a a :*: gToCantor' @t @b b)
      
    (Countable , Finite cb) ->
      let par_s = cb -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      if i < tri_a
         then case cantorSplit i of
                (a , b) -> (gToCantor' @s @a a :*: gToCantor' @t @b b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
              in
              case divModInteger j par_s of
                (# l , s #) ->
                  let c1 = (l + tri_l) - s
                      c2 = s
                      (a , b) = (c1 , c2)
                  in
                  (gToCantor' @s @a a :*: gToCantor' @t @b b)
    _ -> case cantorSplit i of
      (a , b) -> (gToCantor' @s @a a :*: gToCantor' @t @b b)
  
  gFromCantor' (a :*: b) = case (gCardinality' @s @a , gCardinality' @t @b) of
    (Finite ca , Finite cb) ->
      let (x , y) = (gFromCantor' @s @a a , gFromCantor' @t @b b)
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
    (Finite ca , Countable) ->
      let (x , y) = (gFromCantor' @s @a a , gFromCantor' @t @b b)
          par_s = ca
          tri_l = par_s - 1
      in
      if y < tri_l - x
         then cantorUnsplit $ (x , y)
         else let (x' , y') = (x , y - (tri_l - x))
                  tri_a = (tri_l * (tri_l + 1)) `div` 2
              in
              tri_a + x' + y' * par_s
    (Countable , Finite cb) ->
      let (x , y) = (gFromCantor' @s @a a , gFromCantor' @t @b b)
          par_s = cb
          tri_l = par_s - 1
      in
      if y < tri_l - x
         then cantorUnsplit $ (x , y)
         else let (x' , y') = (y , x - (tri_l - y))
                  tri_a = (tri_l * (tri_l + 1)) `div` 2
              in
              tri_a + x' + y' * par_s
    _ -> cantorUnsplit (gFromCantor' @s @a a , gFromCantor' @t @b b)


-- in this instance, make sure we head towards the exit if there is one, otherwise we can get
-- stuck endlessly in the labyrinth
instance (GCantor' s a , GCantor' t b) => GCantor' (s ':+ t) (a :+: b) where
  hasExit = hasExit @s @a || hasExit @t @b
  gCardinality' = case (gCardinality' @s @a , gCardinality' @t @b) of
    (Finite i , Finite j) -> Finite (i + j)
    _ -> Countable

  gToCantor' i = case (gCardinality' @s @a , gCardinality' @t @b) of
    (Finite ca , Finite cb) -> if i < 2 * min ca cb
      then case divModInteger i 2 of
        (# k , 0 #) -> L1 $ gToCantor' @s @a k
        (# k , _ #) -> R1 $ gToCantor' @t @b k
      else if ca > cb
           then L1 $ gToCantor' @s @a (i - cb)
           else R1 $ gToCantor' @t @b (i - ca)
    (Finite ca , Countable) -> if i < 2 * ca
      then case divModInteger i 2 of
        (# k , 0 #) -> L1 $ gToCantor' @s @a k
        (# k , _ #) -> R1 $ gToCantor' @t @b k
      else R1 $ gToCantor' @t @b (i - ca)
    (Countable , Finite _) -> case gToCantor' @(t ':+ s) @(b :+: a) i of
      L1 x -> R1 x
      R1 x -> L1 x
    _ -> if not (hasExit @s @a) && hasExit @t @b
            then case gToCantor' @(t ':+ s) @(b :+: a) i of
              L1 x -> R1 x
              R1 x -> L1 x
            else case divModInteger i 2 of
             (# k , 0 #) -> L1 $ gToCantor' @s @a k
             (# k , _ #) -> R1 $ gToCantor' @t @b k

  gFromCantor' (L1 x) = case gCardinality' @t @b of
    Finite cb -> case gCardinality' @s @a of
      Countable -> gFromCantor' @(t ':+ s) @(b :+: a) $ R1 x
      _ -> case gFromCantor' @s @a x of
        0 -> 0
        i -> i + min cb i
    Countable -> case gCardinality' @s @a of
      Countable -> if not (hasExit @s @a) && hasExit @t @b
        then gFromCantor' @(t ':+ s) @(b :+: a) $ R1 x
        else case gFromCantor' @s @a x of
          0 -> 0
          i -> 2 * i
      _ -> case gFromCantor' @s @a x of
        0 -> 0
        i -> 2 * i
  gFromCantor' (R1 x) = case gCardinality' @s @a of
    Finite ca -> case gFromCantor' @t @b x of
      0 -> 1
      i -> i + min ca (i + 1)
    Countable -> case gCardinality' @t @b of
      Finite _ -> gFromCantor' @(t ':+ s) @(b :+: a) $ L1 x
      Countable -> if not (hasExit @s @a) && hasExit @t @b
        then gFromCantor' @(t ':+ s) @(b :+: a) $ L1 x
        else case gFromCantor' @t @b x of
          0 -> 1
          i -> 2 * i + 1

instance GCantor' s f => GCantor' s (M1 i t f) where
  hasExit = hasExit @s @f

  gCardinality' = gCardinality' @s @f
  
  gToCantor' = M1 . gToCantor' @s @f
  
  gFromCantor' (M1 x) = gFromCantor' @s @f x

