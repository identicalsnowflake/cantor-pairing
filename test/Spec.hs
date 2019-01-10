{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import GHC.Generics (Generic)
import Test.Hspec
import Data.Void

import Cantor

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
        e = take 500 cantorEnumeration

