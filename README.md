# cantor-pairing

This package implements a beefed-up version of `Enum` via GHC generics called `Cantor` which works for both finite and countably-infinite types.

## Example
```haskell
import GHC.Generics
import Cantor

data MyType = MyType {
    value1 :: [ Maybe Bool ]
  , value2 :: Integer
  } deriving (Generic,Cantor,Show)

example :: IO ()
example = do
  putStrLn "The first 5 elements of the enumeration are:"
  print $ take 5 xs
  where
    xs :: [ MyType ]
    xs = cantorEnumeration

```
This should work nicely even with simple inductive types:

## Recursive example
```haskell
data Tree a = Leaf | Branch (Tree a) a (Tree a) deriving (Generic,Cantor)
```

If your type is finite, you can specify this by deriving the `Finite` typeclass, which is a subclass of `Cantor`:

## Finite example
```haskell
data Color = Red | Green | Blue deriving (Generic,Cantor,Finite)
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

Once you have a valid instance of `Cantor a`, you may lazily inspect all values of the type using `cantorEnumeration :: [ a ]` and convert a point to and from its integer encoding using `toCantor :: Integer -> a` and `fromCantor :: a -> Integer`.

