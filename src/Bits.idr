module Bits

%access public export
%default total

||| Ceiling of log_2 for `Nat`s.
||| This is a bit module, so for convenience, we say clog2 0 = 0
clog2 : Nat -> Nat
clog2 Z = 0
clog2 (S Z) = 0
clog2 (S (S n)) = let y1 = log2NZ (S (S n)) SIsNotZ
                      y2 = log2NZ (S n) SIsNotZ in
                  if y1 == y2 then y1+1 else y1

||| Floor of log_2 for `Nat`s.
||| This is a bit module, so for convenience, we say flog2 0 = 0
flog2 : Nat -> Nat
flog2  Z    = 0
flog2 (S z) = log2NZ (S z) SIsNotZ

||| Round a `Double` to the closest `Nat`
round : Double -> Nat
round x = cast $ cast {to=Integer} (x+0.5)

||| Version of flog2 for `Double`
flog2Approx : Double -> Nat
flog2Approx = flog2 . round

||| Conversion of maximum unsigned value, to minimum number of bits
maxToBits : Nat -> Nat
maxToBits = clog2 . (+1)

||| Conversion of bits to maximum unsigned value
bitsToMax : Nat -> Nat
bitsToMax = Nat.pred . power 2
