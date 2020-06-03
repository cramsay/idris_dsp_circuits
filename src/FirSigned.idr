module FirSigned

import ClosedInt
import Synchronous

import Data.Vect
import Data.ZZ
import Data.Bits

%access export
%default total

-- The Vect implementation of Foldable breaks a proof here...
-- Let's redefine sum for now without using fold
%hide sum
sum :  Num a => Vect n a -> a
sum [] = 0
sum (x::xs) = x + sum xs

||| Combinatorial dot product over `ClosedInt`s
dotProd : (ws : Vect j ZZ)
        -> Vect j (ClosedInt n m)
        -> ClosedInt (sum $ map (multLo n m) ws)
                     (sum $ map (multHi n m) ws)
dotProd []        []        = zeros
dotProd (w :: ws) (x :: xs) = add (multConst x w) (dotProd ws xs)

||| Synchronous FIR over `ClosedInt`s
fir : (ws : Vect j ZZ)
   -> Stream (ClosedInt n m)
   -> Stream (ClosedInt (sum $ map (multLo n m) ws)
                        (sum $ map (multHi n m) ws))
fir {j} ws x = liftA (dotProd ws) (window j zeros x)

-- TODO Consider a wrapper for this with Signed

||| Example of simulating `fir`
main : IO ()
main = do let dut = fir [1,-1,2]
          let inp = map (saturate {n=0} {m=6}) $ counterFrom 0 {ty=ZZ}
          let out = take 5 $ simulate dut inp
          putStrLn $ show out

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
