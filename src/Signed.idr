module Signed

%access export
%default total

||| A signed binary number represented with `n` bits
data Signed : (n : Nat) -> Type where
  ||| Built from an underlying integer
  S : Integer -> Signed n

-- We could require a proof for this contructor that our Integer is indeed in
-- the range 0 -> 2*n-1. We don't bother because only (trusted) functions in
-- this module can use the constructor.

||| Cast instance for `Signed n` to an integer
Cast (Signed n) Integer where
  cast (S x) = x

||| Eq instacne for equality of `Signed n`
Eq (Signed n) where
  (==) (S x) (S y) = x==y

||| Ord instance for ordering of `Signed n`
Ord (Signed n) where
  compare (S x) (S y) = compare x y

||| MinBound instance for generating extremes of `Signed n`
MinBound (Signed n) where
  minBound = S . negate . cast . power 2 $ n `minus` 1

||| MaxBound instance for generating extremes of `Signed n`
MaxBound (Signed n) where
  maxBound = S $ cast (power 2 $ n `minus` 1) - 1

||| Safely create an `Signed n` from an Integer using saturation
saturate : Integer -> Signed n
saturate x = let tryS = S {n} x
             in if tryS > maxBound then maxBound else
                if tryS < minBound then minBound else tryS

||| Num instance for saturating arithmetic with `Signed n`
Num (Signed n) where
  (+) (S x) (S y) = saturate $ (x+y)
  (*) (S x) (S y) = saturate $ (x*y)
  fromInteger x   = saturate $ x

||| Show instance for printing `Signed n`
Show (Signed n) where
  show (S x) = "S" ++ show n ++ " " ++ show x
