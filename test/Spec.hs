{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import Control.Exception
import Data.Void
import GHC.Generics (Generic)
import Numeric.Natural
import Test.Hspec
import Test.QuickCheck

import Cantor
import Cantor.Huge

data TreeL a = NodeL | BranchL (TreeL a) a (TreeL a) deriving (Generic,Eq)

instance Cantor a => Cantor (TreeL a)

data TreeR a = BranchR (TreeR a) a (TreeR a) | NodeR deriving (Generic,Eq)

instance Cantor a => Cantor (TreeR a)


instance (Finite a , Cantor b) => Eq (a -> b) where
  (==) f g = fmap (fromCantor . f) cantorEnumeration == fmap (fromCantor . g) cantorEnumeration

data C = R | G | B deriving (Generic,Eq,Ord,Show,Cantor,Finite)


main :: IO ()
main = hspec $ do
  describe "cardinality" $ do
    it "returns 3 for the cardinality of C" $ do
      (fCardinality @C) `shouldBe` 3

    it "returns 9 for the cardinality of C x C" $
      (fCardinality @(C , C)) `shouldBe` 9

    it "returns 6 for the cardinality of Bool x C" $
      (fCardinality @(Bool , C)) `shouldBe` 6

    it "returns 9 for the cardinality of C x Bool" $
      (fCardinality @(C , Bool)) `shouldBe` 6

    it "returns 0 for the cardinality of Void x Bool" $
      (fCardinality @(Void , Bool)) `shouldBe` 0

    it "returns 0 for the cardinality of Bool x Void" $
      (fCardinality @(Bool , Void)) `shouldBe` 0

    it "returns Countable for the cardinality of Bool x Integer" $
      (cardinality @(Bool , Integer)) `shouldBe` Countable

    it "returns Countable for the cardinality of Integer x Bool" $
      (cardinality @(Integer , Bool)) `shouldBe` Countable

    it "returns Finite 0 for the cardinality of Void x Integer" $
      (cardinality @(Void , Integer)) `shouldBe` Finite 0

    it "returns Finite 0 for the cardinality of Integer x Void" $
      (cardinality @(Integer , Void)) `shouldBe` Finite 0

    it "returns 8 for the cardinality of (C -> Bool)" $
      (fCardinality @(C -> Bool)) `shouldBe` 8

    it "returns 9 for the cardinality of (Bool -> C)" $
      (fCardinality @(Bool -> C)) `shouldBe` 9

    it "returns Countable for the cardinality of (Bool -> Integer)" $
      (cardinality @(Bool -> Integer)) `shouldBe` Countable

    it "returns Countable for the cardinality of [ C ]" $
      (cardinality @([ C ])) `shouldBe` Countable


  describe "uniqueness and isomorphism for finite types" $ do
    it "for C" $
      (fcheckUISO @C) `shouldBe` True

    it "for C x Bool" $
      (fcheckUISO @(C , Bool)) `shouldBe` True

    it "for Bool x C" $
      (fcheckUISO @(Bool , C)) `shouldBe` True

    it "for (Bool x Bool) x C" $
      (fcheckUISO @((Bool , Bool) , C)) `shouldBe` True

    it "for Void x C" $
      (fcheckUISO @(Void , C)) `shouldBe` True

    it "for C x Void" $
      (fcheckUISO @(C , Void)) `shouldBe` True

    it "for C -> Bool" $
      (fcheckUISO @(C -> Bool)) `shouldBe` True

    it "for Bool -> C" $
      (fcheckUISO @(Bool -> C)) `shouldBe` True

  describe "uniqueness and isomorphism for countable types" $ do
    it "for C x Integer" $
      (checkUISO @(C , Integer)) `shouldBe` True

    it "for Integer x C" $
      (checkUISO @(C , Integer)) `shouldBe` True

    it "for Integer x Integer" $
      (checkUISO @(Integer , Integer)) `shouldBe` True

    it "for C -> Integer" $
      (checkUISO @(C -> Integer)) `shouldBe` True

    it "for [ C -> Integer ]" $
      (checkUISO @([ (C -> Integer) ])) `shouldBe` True

    it "for TreeL Bool" $
      (checkUISO @(TreeL Bool)) `shouldBe` True

    it "for TreeR Bool" $
      (checkUISO @(TreeR Bool)) `shouldBe` True

  describe "function enumeration even for large domains" $ do
    it "should be fast" $
      (head (cantorEnumeration @(Word -> Int)) 42173) `shouldBe` 0

  describe "instance Ord Huge" $ do
    it "compares atomic expressions" $ property prop_compare_atomic
    it "compares against constants"  $ property $
      \(NonNegative n) h -> isSmall h ==>
        fromInteger n `compare` h === fromInteger n `compare` eval h
    it "matches Ord Natural" $ property $
      \x y -> isSmall x ==> isSmall y ==>
        x `compare` y === eval x `compare` eval y
    it "is reflexive" $ property $
      \(x :: Huge) -> x `compare` x === EQ

  where
    fcheckUISO :: forall a . (Eq a , Finite a) => Bool
    fcheckUISO = e == fmap (toCantor . fromCantor) e
      where
        e :: [ a ]
        e = cantorEnumeration

    checkUISO :: forall a . (Eq a , Cantor a) => Bool
    checkUISO = e == fmap (toCantor . fromCantor) e
      where
        e :: [ a ]
        e = take 5000 cantorEnumeration

-------------------------------------------------------------------------------
-- Huge

instance Arbitrary Huge where
  arbitrary = frequency
    [ (50, fromInteger . (`mod` 6) <$> arbitrary)
    , (15, (+) <$> arbitrary <*> arbitrary)
    , (15, (*) <$> arbitrary <*> arbitrary)
    , ( 5, pow <$> arbitrary <*> arbitrary)
    ]

cap :: Natural
cap = 2 ^ (2 ^ (16 :: Int) :: Int)

data Capped = Capped Natural | TooLarge
  deriving (Eq, Ord, Show)

instance Num Capped where
  _ + TooLarge = TooLarge
  TooLarge + _ = TooLarge
  Capped x + Capped y = fromIntegral (x + y)

  _ * TooLarge = TooLarge
  TooLarge * _ = TooLarge
  Capped x * Capped y = fromIntegral (x * y)

  negate = throw Underflow
  abs = id
  signum = const 1

  fromInteger n = let m = fromInteger n in if m > cap then TooLarge else Capped m

evalCapped :: Huge -> Capped
evalCapped = evalWith f
  where
    f :: Capped -> Capped -> Capped
    f _ TooLarge   = TooLarge
    f x (Capped y) = x ^ y

isSmall :: Huge -> Bool
isSmall = (/= TooLarge) . evalCapped

prop_compare_atomic
  :: NonNegative Integer
  -> NonNegative Integer
  -> NonNegative Integer
  -> NonNegative Integer
  -> Property
prop_compare_atomic (NonNegative x) (NonNegative y) (NonNegative u) (NonNegative v) =
  foldl (.&&.) (property True) props
  where
    funcs = [const, (+), (*), pow]
    props = [ prop (fxy (fromInteger x) (fromInteger y)) (fuv (fromInteger u) (fromInteger v)) | fxy <- funcs, fuv <- funcs ]
    prop xy uv = xy `compare` uv === eval xy `compare` (eval uv :: Natural)
