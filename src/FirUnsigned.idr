module FirUnsigned

import Bits
import Bounded
import Synchronous
import Unsigned

import Data.Vect
import Data.Bits

%access export
%default total

-- The Vect implementation of Foldable breaks a proof here...
-- Let's redefine sum for now without using fold
%hide sum
sum :  Num a => Vect n a -> a
sum [] = 0
sum (x::xs) = x + sum xs

-- Proof of distributative property for `Bounded`'s ranges.
-- Required for the readability (for the IEEE reader!) of the type of `dotProd`
dotProdDistrib : (n, w, j : Nat) -> (ws : Vect j Nat)
              -> Bounded (n * (w + sum ws)) = Bounded (n * w + n * sum ws)
dotProdDistrib n w j ws = rewrite multDistributesOverPlusRight n w (sum ws) in Refl

||| Combinatorial dot product over `Bounded`s
dotProd : (ws : Vect j Nat)
       -> Vect j (Bounded n)
       -> Bounded (n * sum ws)
dotProd {j=Z} _ _ = zeros
dotProd {j=S l} {n} (w :: ws) (x :: xs) =
  let y = add (mulConst x w) (dotProd ws xs)
  in rewrite dotProdDistrib n w l ws in y

||| Synchronous FIR over `Bounded`s
fir : (ws : Vect j Nat)
   -> Stream (Bounded n)
   -> Stream (Bounded (n * sum ws))
fir {j} ws x = liftA (dotProd ws) (window j zeros x)

||| A wrapper for `fir` using `Unsigned`s`, more familiar to most IEEE readers
firU : (ws : Vect j Nat) -> Stream (Unsigned n)
    -> Stream (Unsigned (maxToBits $ (bitsToMax n) * (sum ws)))
firU ws = map toUnsigned . fir ws . map fromUnsigned

||| Example of simulating `firU`
main : IO ()
main = do let dut = firU [1,3,2]
          let inp = map (saturate {n=4}) $ counterFrom 0
          let out = take 5 $ simulate dut inp
          putStrLn $ show out

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
