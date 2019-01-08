{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
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
-- A warning: this package will work with recursive types, but you *must* manually specify the cardinality. This unfortunately is necessary due to GHC generics marking all fields as recursive, regardless of whether or not they actually are. Still, it's straightforward to manually specify the cardinality:
-- 
-- = Recursive example
-- @
-- data Tree a = Leaf | Branch (Tree a) a (Tree a) deriving (Generic)
--
-- instance Cantor a => Cantor (Tree a) where
--   cardinality = Countable
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

module Cantor (
         cantorEnumeration
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
import Data.Functor.Const
import Data.Proxy
import Math.NumberTheory.Powers.Squares (integerSquareRoot')
import Data.Void
import Data.Bits (finiteBitSize)
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
  
  default cardinality :: (GCantor (Rep a)) => Cardinality
  cardinality = gCardinality @(Rep a)
  
  toCantor :: Integer -> a -- ideally this should be `Fin n -> a` (for finite types)
                           -- or `N` (for countably infinite types).
                           -- I chose not to use `Natural` from `GHC.Natural`
                           -- because it's turned out to be a huge pain and integrates
                           -- poorly with the haskell ecosystem
  default toCantor :: (Generic a , GCantor (Rep a)) => Integer -> a
  toCantor = to . gToCantor

  fromCantor :: a -> Integer
  default fromCantor :: (Generic a , GCantor (Rep a)) => a -> Integer
  fromCantor = gFromCantor . from
  

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

instance Finite Word
instance Cantor Word where
  cardinality = Finite $ 2 ^ (finiteBitSize @Word undefined)
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
instance Cantor a => Cantor (Const a b)
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
instance Finite a => Finite (Const a b)
instance Finite a => Finite (Option a)
instance Finite a => Finite (Min a)
instance Finite a => Finite (Max a)
instance Finite (Proxy a)
instance (Finite a , Finite b) => Finite (Arg a b)

instance Finite a => Finite (Maybe a)
instance (Finite a , Finite b) => Finite (Either a b)


-- due to generics issues below, when making recursive instances, cardinality must
-- manually be specified
instance Cantor a => Cantor [ a ] where
  cardinality = Countable

-- how to memoise gCardinality??
class GCantor f where
  gCardinality :: Cardinality

  gToCantor :: Integer -> f a
  gFromCantor :: f a -> Integer

instance GCantor V1 where
  gCardinality = Finite 0
  gToCantor _ = error "Cantor bounds error."
  gFromCantor _ = error "Cantor bounds error."

instance GCantor U1 where
  gCardinality = Finite 1
  gToCantor _ = U1
  gFromCantor _ = 0

nary :: Integer -> ESpace a -> ESpace [ a ]
nary 0 _ = undefined
nary 1 (ESpace c t f) = ESpace c (\i -> [ t i ]) $ \case
  [ x ] -> f x
  _ -> undefined
nary i es = case es *** nary (i - 1) es of
  ESpace c t f -> ESpace c t' f'
    where
      t' j = case t j of
        (a , as) -> a : as

      f' (a : as) = f (a , as)
      f' _ = undefined

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

instance (GCantor a , GCantor b) => GCantor (a :*: b) where
  gCardinality = case (gCardinality @a , gCardinality @b) of
    (Finite i , Finite j) -> Finite (i * j)
    (Finite 0 , _) -> Finite 0
    (_ , Finite 0) -> Finite 0
    _ -> Countable

  gToCantor i = case (gCardinality @a , gCardinality @b) of
    (Finite ca , Finite cb) ->
      let par_s = min ca cb -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      -- optimisation - if tri_l is 0, one or both of these is trivial and we have a line
      if i < tri_a
         then -- we're in the triangle, so just use cantor
              case cantorSplit i of
                (a , b) -> (gToCantor a :*: gToCantor b)
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
                          (gToCantor a :*: gToCantor b)
                 else let k = j - par_a
                          l = tri_a - (k + 1) in
                      case cantorSplit l of
                        (a , b) -> (gToCantor (ca - (a + 1)) :*: gToCantor (cb - (b + 1)))
    (Finite ca , Countable) ->
      let par_s = ca -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      if i < tri_a
         then case cantorSplit i of
                (a , b) -> (gToCantor a :*: gToCantor b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
              in
              case divModInteger j par_s of
                (# l , s #) ->
                  let c1 = (l + tri_l) - s
                      c2 = s
                      (a , b) = (c2 , c1)
                  in
                  (gToCantor a :*: gToCantor b)
      
    (Countable , Finite cb) ->
      let par_s = cb -- small altitude of the parallelogram
          tri_l = par_s - 1
          tri_a = (tri_l * (tri_l + 1)) `div` 2
      in
      if i < tri_a
         then case cantorSplit i of
                (a , b) -> (gToCantor a :*: gToCantor b)
         else let j = i - tri_a -- shadowing would make this so much safer, alas...
              in
              case divModInteger j par_s of
                (# l , s #) ->
                  let c1 = (l + tri_l) - s
                      c2 = s
                      (a , b) = (c1 , c2)
                  in
                  (gToCantor a :*: gToCantor b)
    _ -> case cantorSplit i of
      (a , b) -> (gToCantor a :*: gToCantor b)
  
  gFromCantor (a :*: b) = case (gCardinality @a , gCardinality @b) of
    (Finite ca , Finite cb) ->
      let (x , y) = (gFromCantor a , gFromCantor b)
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
      let (x , y) = (gFromCantor a , gFromCantor b)
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
      let (x , y) = (gFromCantor a , gFromCantor b)
          par_s = cb
          tri_l = par_s - 1
      in
      if y < tri_l - x
         then cantorUnsplit $ (x , y)
         else let (x' , y') = (y , x - (tri_l - y))
                  tri_a = (tri_l * (tri_l + 1)) `div` 2
              in
              tri_a + x' + y' * par_s
    _ -> cantorUnsplit (gFromCantor a , gFromCantor b)

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

instance (GCantor a , GCantor b) => GCantor (a :+: b) where
  gCardinality = case (gCardinality @a , gCardinality @b) of
    (Finite i , Finite j) -> Finite (i + j)
    _ -> Countable

  gToCantor i = case (gCardinality @a , gCardinality @b) of
    (Finite ca , Finite cb) -> if i < 2 * min ca cb
      then case divModInteger i 2 of
        (# k , 0 #) -> L1 $ gToCantor k
        (# k , _ #) -> R1 $ gToCantor k
      else if ca > cb
           then L1 $ gToCantor (i - cb)
           else R1 $ gToCantor (i - ca)
    (Finite ca , Countable) -> if i < 2 * ca
      then case divModInteger i 2 of
        (# k , 0 #) -> L1 $ gToCantor k
        (# k , _ #) -> R1 $ gToCantor k
      else R1 $ gToCantor (i - ca)
    (Countable , Finite _) -> case gToCantor i of
      L1 x -> R1 x
      R1 x -> L1 x
    -- (Countable , Finite cb) -> if i < 2 * cb
    --   then case divModInteger i 2 of
    --     (# k , 1 #) -> L1 $ gToCantor k -- bias the finite half or risk looping!
    --     (# k , _ #) -> R1 $ gToCantor k
    --   else L1 $ gToCantor (i - cb)
    _ -> case divModInteger i 2 of
      (# k , 0 #) -> L1 $ gToCantor k
      (# k , _ #) -> R1 $ gToCantor k

  gFromCantor (L1 x) = case gCardinality @b of
    Finite cb -> case gCardinality @a of
      Countable -> gFromCantor @(b :+: a) $ R1 x
      _ -> case gFromCantor x of
        0 -> 0
        i -> i + min cb i
    Countable -> case gFromCantor x of
      0 -> 0
      i -> 2 * i
  gFromCantor (R1 x) = case gCardinality @a of
    Finite ca -> case gFromCantor x of
      0 -> 1
      i -> i + min ca (i + 1)
    Countable -> case gCardinality @b of
      Finite _ -> gFromCantor @(b :+: a) $ L1 x
      Countable -> case gFromCantor x of
        0 -> 1
        i -> 2 * i + 1
 
-- this SHOULD work at least in basic cases,
-- but GHC generic deriving does not properly distinguish between
-- K1 i for non-recursive cases and K1 R for recursive cases -______-
-- instance {-# OVERLAPPING #-} Cantor a => GCantor (K1 R a) where
--   gCardinality = Countable
--   gToCantor i = K1 $ toCantor i
--   gFromCantor (K1 x) = fromCantor x

instance (Cantor a) => GCantor (K1 i a) where
  gCardinality = cardinality @a

  gToCantor x = K1 (toCantor x)

  gFromCantor (K1 x) = fromCantor x

instance (GCantor f) => GCantor (M1 i t f) where
  gCardinality = gCardinality @f

  gToCantor x = M1 (gToCantor x)

  gFromCantor (M1 x) = gFromCantor x

