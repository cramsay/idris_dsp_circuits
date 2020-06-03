module Bounded

import Bits
import Unsigned

%access export
%default total

||| An unsigned number represented bounded within the range [0,`n`], inclusive
data Bounded : (n: Nat) -> Type where
  B : (n:Nat) -> (m:Nat) -> Bounded m

-- We should consider requiring a proof that 0 <= m <= n in this
-- constructor.

||| Show instance for printing `Bounded n`
Show (Bounded n) where
  show (B x n) = "B" ++ show n ++ " " ++ show x

||| Eq instance for equality of `Bounded n`s.
||| Ranges *and* values must be equal.
Eq (Bounded n) where
  (==) (B x n) (B y n) = x==y

||| Ord instance for ordering of `Bounded n`s
Ord (Bounded n) where
 compare (B x n) (B y n) = compare x y

||| MinBound instance for generating extremes of `Signed n`
MinBound (Bounded n) where
  minBound = B 0 n

||| MaxBound instance for generating extremes of `Signed n`
MaxBound (Bounded n) where
  maxBound = B n n

--------------------------------------------------------------------------------
-- Conversion functions
--------------------------------------------------------------------------------

||| Conversion from `Unsigned` to `Bounded`
fromUnsigned : Unsigned n -> Bounded (bitsToMax n)
fromUnsigned {n} x = B (fromInteger $ cast x) (bitsToMax n)

||| Conversion from `Bounded` to `Unsigned`
toUnsigned : Bounded n -> Unsigned (maxToBits n)
toUnsigned (B x _) = saturate (cast x)

||| Generate a `Bounded n` instance of zeros
zeros : Bounded n
zeros = B 0 n

--------------------------------------------------------------------------------
-- Bounded arithmetic functions
--------------------------------------------------------------------------------

||| Add two `Bounded`s
add : Bounded n ->Bounded m -> Bounded (n+m)
add (B x n) (B y m) = B (x+y) (n+m)

||| Multiply two `Bounded`s
mult : Bounded n ->Bounded m -> Bounded (n*m)
mult (B x n) (B y m) = B (x*y) (n*m)

||| Add a `Bounded` to a `Nat`
addConst : Bounded n -> (m: Nat) -> Bounded (n+m)
addConst (B x n) m = B (x+m) (n+m)

||| Multiply a `Bounded` by a `Nat`
mulConst : Bounded n -> (m: Nat) -> Bounded (n*m)
mulConst (B x n) m = B (x*m) (n*m)

-- TODO consider making Bounded just a specialisation of ClosedInt
