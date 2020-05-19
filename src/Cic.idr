-- Recursive binomial expansion
nChooseK : (n: Nat) -> (k: Nat) -> Nat
nChooseK n Z = 1
nChooseK Z (S k) = 0
nChooseK (S n) (S k) = nChooseK n k + nChooseK n (S k)

-- h_j(k), from eqn 9b
hjk : (r : Nat) -> (n : Nat) -> (m : Nat) -> (j : Nat) -> (k : Nat) -> Int
hjk r n m j k = case j <= n of
  True  => sum $ map (\l => pow (-1) l * cast (
                              (nChooseK n l) *
                              (nChooseK ((n `minus` j)+(k `minus` r*m*l)) (k `minus` r*m*l)))
                     ) [0..(k `divNat` (r*m))]
  False => pow (-1) k * cast (nChooseK (minus (2*n+1) j) k)

fj : (r : Nat) -> (n : Nat) -> (m : Nat) -> (j : Nat) -> Double
fj r n m j = case j == 2*n+1 of
  True => 1.0
  False => sqrt . cast . sum $ map (\k=>pow (hjk r n m j k) 2) [0..((r*m `minus` 1) * n + j `minus` 1)]

clog2B : Nat -> Nat
clog2B Z = 0
clog2B (S Z) = 0
clog2B (S (S n)) = let y1 = log2NZ (S (S n)) SIsNotZ
                       y2 = log2NZ (S n) SIsNotZ
                   in if y1 == y2 then y1+1 else y1

flog2B : Nat -> Nat
flog2B Z = 0
flog2B (S z) = log2 (S z)

bmax : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> Nat
bmax r n m bin = bin + n * clog2B (r*m)

eT2n1 : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> (bout : Nat) -> Nat
eT2n1 r n m bin bout = pow 2 $ bmax r n m bin `minus` bout

sigmaT2n1 : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> (bout : Nat) -> Double
sigmaT2n1 r n m bin bout = sqrt $ cast (pow  (eT2n1 r n m bin bout) 2) / 12.0

-- Eqn 21 but we use log laws to avoid errors with repeated rounding
bj : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> (bout : Nat) -> (j : Nat) -> Nat
bj r n m bin bout j = flog2B . cast . cast {to=Integer} . floor $ (sigmaT2n1 r n m bin bout) * (sqrt $ 6.0 / (cast n)) / fj r n m j

cicAccPruned : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> (bout : Nat) -> (j : Nat) -> Nat
cicAccPruned r n m bin bout j = if j==0 then bmax r n m bin else
                                if j>=(2*n+1) then bout else
                                bmax r n m bin `minus` bj r n m bin bout j


-- Unsigned defs
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

prune : Unsigned n -> Unsigned m
prune {n} {m} (U x) = U $ x `div` (pow 2 (n `minus` m))

extend : Unsigned n -> Unsigned m
extend (U x) = U x

sub : Unsigned n -> Unsigned n -> Unsigned n
sub (U x) (U y) = U (x-y)

-- CIC sim

delay : a -> Stream a -> Stream a
delay a s = a :: s

integrate : Stream (Unsigned n) -> Stream (Unsigned n)
integrate xs = map (\(a,b)=>a+b) $ zip xs (delay 0 $ integrate xs)

comb : (m : Nat) -> Stream (Unsigned n) -> Stream (Unsigned n)
comb _ xs = map (\(a,b)=>a `sub` b) $ zip xs (delay 0 xs) -- TODO Delay by m... and get

-- TODO implement rate change with enables?

cicDecimateStepIn : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> (bout : Nat) -> Stream (Unsigned bin) -> Stream (Unsigned (cicAccPruned r n m bin bout 0))
cicDecimateStepIn _ _ _ _ _ = map extend

cicDecimateStepI : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> (bout : Nat) -> (j : Nat) -> Stream (Unsigned (cicAccPruned r n m bin bout j)) -> Stream (Unsigned (cicAccPruned r n m bin bout (S j)))
cicDecimateStepI _ _ _ _ _ _ = map prune . integrate

cicDecimateStepC : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> (bout : Nat) -> (j : Nat) -> Stream (Unsigned (cicAccPruned r n m bin bout j)) -> Stream (Unsigned (cicAccPruned r n m bin bout (S j)))
cicDecimateStepC _ _ m _ _ _ = map prune . comb m

  ---- TODO Make wordlengths implicit?

cicDecimateRec : (r : Nat) -> (n : Nat) -> (m : Nat) -> (bin : Nat) -> (bout : Nat) -> (j : Nat) -> Stream (Unsigned (cicAccPruned r n m bin bout 0)) -> Stream (Unsigned (cicAccPruned r n m bin bout (S j)))
cicDecimateRec r n m bin bout  Z    xs = cicDecimateStepI r n m bin bout Z xs
cicDecimateRec r n m bin bout (S j) xs = let recStep = cicDecimateRec r n m bin bout j xs
                                             newStep  =  if (S j)<n then cicDecimateStepI r n m bin bout (S j)
                                                       else             cicDecimateStepC r n m bin bout (S j)
                                         in newStep recStep

                                    -- TODO Worth trying to prove that cicAccPruned r n m bin bout (2*n+1)) == bout
cicDecimate : (r : Nat) -> (n : Nat) -> (m : Nat) -> Stream (Unsigned bin) -> Stream (Unsigned bout)
cicDecimate {bin} {bout} r n m xs = map prune $ cicDecimateRec r n m bin bout (2*n) $ cicDecimateStepIn r n m bin bout xs

main : IO ()
main = print $ map (bj 8 3 1 12 12) [1..6]
