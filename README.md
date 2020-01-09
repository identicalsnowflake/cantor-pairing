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
This should work nicely even with simple inductive types:

## Recursive example
```haskell
data Tree a = Leaf | Branch (Tree a) a (Tree a) deriving (Generic)

instance Cantor a => Cantor (Tree a)
```

If your type is finite, you can specify this by deriving the `Finite` typeclass, which is a subclass of `Cantor`:

## Finite example
```haskell
data Color = Red | Green | Blue deriving (Generic)

instance Cantor Color
instance Finite Color
```

## Mutually-recursive types

If you have mutually-recursive types, unfortunately you'll need to manually specify the cardinality for now, but you can still get the to/from encodings for free:

```haskell
data Foo = FooNil | Foo Bool Bar deriving (Generic,Show)
data Bar = BarNil | Bar Bool Foo deriving (Generic,Show)

instance Cantor Foo where
  cardinality = Countable
instance Cantor Bar
```

