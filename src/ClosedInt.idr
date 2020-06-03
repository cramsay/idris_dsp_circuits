module ClosedInt

import Bits
import Signed
import Data.ZZ

%access export
%default total

||| A value in the closed (integer) interval [n,m]
data ClosedInt : (n: ZZ) -> (m: ZZ) -> Type where
  ||| Built with a ZZ
  CI : {n, m: ZZ} -> (x:ZZ) -> ClosedInt n m

-- Consider adding a proof that n <= x <= m using some ZZ proof types, similar
-- to Nat's LTE type. See
-- https://stackoverflow.com/questions/46066253/lte-for-integers-zz
-- for ideas

||| Show instance for printing `ClosedInt`s
Show (ClosedInt n m) where
  show {n} {m} (CI x) = "CI(" ++ show n ++ "," ++ show m ++ ") " ++ show x

||| Eq instance for equality of `ClosedInt`s
Eq (ClosedInt n m) where
  (==) (CI x) (CI y) = x==y

||| Ord instance for ordering of `ClosedInt`s
Ord (ClosedInt n m) where
  compare (CI x) (CI y) = compare x y

||| MinBound instance for generating extremes of `ClosedInt n m`
MinBound (ClosedInt n m) where
  minBound = CI n

||| MaxBound instance for generating extremes of `ClosedInt n m`
MaxBound (ClosedInt n m) where
  maxBound = CI m

||| Generate a `ClosedInt n m` with zeros. The caller must ensure that `n<=0<=m`
zeros : ClosedInt n m
zeros = CI 0

||| Safely create an `Unsigned n` from an Integer using saturation
saturate : ZZ -> ClosedInt n m
saturate x = let tryCI = CI {n} {m} x
             in if tryCI > maxBound then maxBound else
                if tryCI < minBound then minBound else tryCI

--------------------------------------------------------------------------------
-- ClosedInt arithmetic functions
--------------------------------------------------------------------------------

||| Helper function to find high bound of `ClosedInt` scaled by an integer
||| constant
-- public export
multHi : (n, m, a : ZZ) -> ZZ
multHi n m (Pos  k) = m*(Pos  k)
multHi n m (NegS k) = n*(NegS k)

||| Helper function to find low bound of `ClosedInt` scaled by an integer
||| constant
-- public export
multLo : (n, m, a : ZZ) -> ZZ
multLo n m (Pos  k) = n*(Pos  k)
multLo n m (NegS k) = m*(NegS k)

||| Multiply a `ClosedInt` with an integer constant
multConst : ClosedInt n m -> (a : ZZ) -> ClosedInt (multLo n m a) (multHi n m a)
multConst {n}{m} (CI x) a = CI (x*a) {n=multLo n m a} {m=multHi n m a}

||| Add two `ClosedInt`s
add : ClosedInt n m -> ClosedInt a b -> ClosedInt (n+a) (m+b)
add {n}{m}{a}{b} (CI x) (CI y) = CI (x+y) {n=(n+a)} {m=(m+b)}

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
