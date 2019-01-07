# cantor-pairing

Cantor pairing gives us an isomorphism between a single natural number and pairs of natural numbers. This package provides a modern API to this functionality using GHC generics, allowing the encoding of arbitrary combinations of finite or countably infinite types in natural number form.

As a user, all you need to do is derive generic and get the instances for free.

## Example
```haskell
import GHC.Generics
import Cantor

data MyType = MyType {
    value1 :: [ Maybe Bool ]
  , value2 :: Integer
  } deriving (Generic)

instance Cantor MyType
```
A warning: this package will work with recursive types, but you *must* manually specify the cardinality. This unfortunately is necessary due to GHC generics marking all fields as recursive, regardless of whether or not they actually are. Still, it's straightforward to manually specify the cardinality:

## Recursive example
```haskell
data Tree a = Leaf | Branch (Tree a) a (Tree a) deriving (Generic)

instance Cantor a => Cantor (Tree a) where
  cardinality = Countable
```

If your type is finite, you can specify this by deriving the `Finite` typeclass, which is a subclass of `Cantor`:

## Finite example
```haskell
data Color = Red | Green | Blue deriving (Generic)

instance Cantor Color
instance Finite Color
```
