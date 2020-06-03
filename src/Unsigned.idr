module Unsigned

%access export
%default total

||| An unsigned binary number represented with `n` bits
data Unsigned : (n : Nat) -> Type where
  ||| Built from an underlying integer
  U : Integer -> Unsigned n

-- We could require a proof for this contructor that our Integer is indeed in
-- the range 0 -> 2*n-1. We don't bother because only (trusted) functions in
-- this module can use the constructor.

||| Cast instance for `Unsigned n` to an integer
Cast (Unsigned n) Integer where
  cast (U x) = x

||| Eq instacne for equality of `Unsigned n`
Eq (Unsigned n) where
  (==) (U x) (U y) = x==y

||| Ord instance for ordering of `Unsigned n`
Ord (Unsigned n) where
  compare (U x) (U y) = compare x y

||| MinBound instance for generating extremes of `Unsigned n`
MinBound (Unsigned n) where
  minBound = U 0

||| MaxBound instance for generating extremes of `Unsigned n`
MaxBound (Unsigned n) where
  maxBound = U $ cast (power 2 n)-1

||| Safely create an `Unsigned n` from an Integer using saturation
saturate : Integer -> Unsigned n
saturate x = let tryU = U {n} x
             in if tryU > maxBound then maxBound else
                if tryU < minBound then minBound else tryU

||| Num instance for saturating arithmetic with `Unsigned n`
Num (Unsigned n) where
  (+) (U x) (U y) = saturate $ (x+y)
  (*) (U x) (U y) = saturate $ (x*y)
  fromInteger x   = saturate $ x

||| Minus operations for two `Unsigned`s. Note that we cannot implement the Neg
||| typeclass because there are no negative representations.
minus : Unsigned n -> Unsigned n -> Unsigned n
minus (U x) (U y) = U (x-y)

||| Helper function to prove that 2^n for all natural n is not 0
private
powerTwoIsNotZ : (n : Nat) -> Not (power 2 n = 0)
powerTwoIsNotZ n = believe_me -- TODO prove properly

||| Add operations for two `Unsigned`s with wrapping overflow.
addWrap : Unsigned n -> Unsigned n -> Unsigned n
addWrap (U x) (U y) = let max = power 2 n
                          res = cast x + cast y
                      in U . cast $ modNatNZ res max (powerTwoIsNotZ n)

||| Minus operations for two `Unsigned`s with wrapping overflow.
minusWrap : Unsigned n -> Unsigned n -> Unsigned n
minusWrap (U x) (U y) = let max = power 2 n
                            res = max + cast x `minus` cast y
                        in U . cast $ modNatNZ res max (powerTwoIsNotZ n)

||| Show instance for printing `Unsigned n`
Show (Unsigned n) where
  show (U x) = "U" ++ show n ++ " " ++ show x

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
