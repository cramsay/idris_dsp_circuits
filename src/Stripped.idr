import Data.Bits
import Data.Vect

%default total

data Unsigned : (n : Nat) -> Type where
  U : Integer -> Unsigned n

toInteger : Unsigned n -> Integer
toInteger (U x) = x

Eq (Unsigned n) where
  (==) (U x) (U y) = x==y

Ord (Unsigned n) where
 compare (U x) (U y) = compare x y

MinBound (Unsigned n) where
  minBound = U 0

MaxBound (Unsigned n) where
  maxBound = U $ cast (power 2 n)-1

saturate : Unsigned n -> Unsigned n
saturate (U x) = if U {n} x > maxBound then maxBound else
                 if U {n} x < minBound then minBound else U x

Num (Unsigned n) where
  (+) (U x) (U y) = saturate $ U (x+y)
  (*) (U x) (U y) = saturate $ U (x*y)
  fromInteger x   = saturate $ U x

Show (Unsigned n) where
  show (U x) = "U" ++ show n ++ " " ++ show x

data UBounded : (n: Nat) -> Type where
  UB :  (n:Nat) -> (m:Nat) -> UBounded m

Show (UBounded n) where
  show (UB x n) = "UB" ++ show n ++ " " ++ show x

Eq (UBounded n) where
  (==) (UB x n) (UB y n) = x==y

Ord (UBounded n) where
 compare (UB x n) (UB y n) = compare x y

MinBound (UBounded n) where
  minBound = UB 0 n

MaxBound (UBounded n) where
  maxBound = UB n n

clog2B : Nat -> Nat
clog2B Z = 0
clog2B (S Z) = 0
clog2B (S (S n)) = let y1 = log2NZ (S (S n)) SIsNotZ
                       y2 = log2NZ (S n) SIsNotZ in
                   if y1 == y2 then y1+1 else y1

maxToBits : Nat -> Nat
maxToBits = clog2B . (+1)

bitsToMax : Nat -> Nat
bitsToMax = Nat.pred . power 2

fromUnsigned : Unsigned n -> UBounded (bitsToMax n)
fromUnsigned {n} x = UB (fromInteger $ toInteger x) (bitsToMax n)

toUnsigned : UBounded n -> Unsigned (maxToBits n)
toUnsigned (UB x _) = U (cast x)

zeros : UBounded n
zeros = UB 0 n

addUB : UBounded n ->UBounded m -> UBounded (n+m)
addUB (UB x n) (UB y m) = UB (x+y) (n+m)

multUB : UBounded n ->UBounded m -> UBounded (n*m)
multUB (UB x n) (UB y m) = UB (x*y) (n*m)

constAddUB : UBounded n -> (m: Nat) -> UBounded (n+m)
constAddUB (UB x n) m = UB (x+m) (n+m)

constMultUB : UBounded n -> (m: Nat) -> UBounded (n*m)
constMultUB (UB x n) m = UB (x*m) (n*m)

-- So, the Vect implementation of Foldable kinda breaks my proof here...
-- Let's redefine sum for now without using fold
%hide sum
sum :  Num a => Vect n a -> a
sum [] = 0
sum (x::xs) = x + sum xs

firProof : (n : Nat) -> (w: Nat) -> (m : Nat) -> (ws : Vect m Nat) ->
           UBounded (n * (w + sum ws)) = UBounded (n * w + n * sum ws)
firProof n w m ws = rewrite multDistributesOverPlusRight n w (sum ws) in Refl

scaleUB : (n:Nat) -> (m:Nat) -> UBounded n -> UBounded m
scaleUB Z m _ = zeros
scaleUB (S n) m (UB x (S n)) = UB (x * m `div` (S n)) m

streamCountFrom : Nat -> Stream Nat
streamCountFrom n = n::streamCountFrom (n+1)

simulate : (Stream a -> Stream b) -> Stream a -> Stream b
simulate f xs = f xs

delay : a -> Stream a -> Stream a
delay a s = a :: s

window : (n : Nat) -> a -> Stream a -> Stream (Vect n a)
window Z a xs     = pure []
window (S k) a xs = let dl = scanl (flip delay) xs (replicate (k) a)
                    in  sequence dl

firCycle : (ws : Vect n Nat) -> Vect n (UBounded m) -> UBounded (m * sum ws)
firCycle {n=Z} _ _ = zeros
firCycle {n=S l} {m} (w :: ws) (x :: xs) =
  let y = addUB (constMultUB x w) (firCycle ws xs)
  in rewrite firProof m w l ws in y

fir : (ws : Vect n Nat) -> Stream (UBounded m) -> Stream (UBounded (m * sum ws))
fir {n} ws x = liftA (firCycle ws) (window n zeros x)

main : IO ()
main = do let y = take 5 $
                  simulate (fir [1,1])
                  (map (\a=>UB a 10) $ streamCountFrom 0)
          putStrLn (show y)


--firU : (ws : List Nat) -> Unsigned n -> Unsigned (maxToBits $ (bitsToMax n) * (sum ws))
--firU ws x = toUnsigned . fir ws $ fromUnsigned x
--
--main : IO ()
--main = do putStrLn "Gimme a number"
--          x <- getLine
--          let y = firU [3,5,4,1] (U (cast x) {n=8})
--          putStrLn (show y)
--
---- Want to show
----   1) Dependent types let us propagate values of parameters into computations on the types
----      This lets us have things like minimum bit growth throughout an FIR
----
----   2) Even in scenarios where Vivado would make these optimisations, describing it this way lets the designer precisely reason about resource usage when exploring different designs.
----
----   3)  
---- Can I play about with composition of chains
--
--
--movingAvg : UBounded n -> UBounded (n*7)
--movingAvg = fir [1,1,1,1,1,1,1]
--
--aaFilter : UBounded n -> UBounded (n*6)
--aaFilter = fir [2, 0, 2, 0, 2, 0]
--
--circuit : UBounded n -> UBounded m
--circuit x = let y = aaFilter $ aaFilter x
--                --y'= scaleUB {m=2} y
--                z = movingAvg
--            in ?out_val
