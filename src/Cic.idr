module Cic

import Bits
import Synchronous
import Unsigned

import Data.Bits

%access export
%default total

-- See Hogenauer's 1981 paper "An Economical Class of Digital Filters for
-- Decimation and Interpolation". All the equations are referenced against this
-- paper

--------------------------------------------------------------------------------
-- CIC subcircuits
--------------------------------------------------------------------------------

||| Prune an `Unsigned n` down to a smaller `Unsigned m`
prune : Unsigned n -> Unsigned m
prune {n} {m} x = saturate . cast $
  shiftR (cast . cast {to=Double} $ cast x {to=Integer}) -- Horrible!
         (cast $ n `minus` m)

||| Extend an `Unsigned n` up to a larger `Unsigned m`
extend : Unsigned n -> Unsigned m
extend = saturate . cast

||| Integrator circuit
partial
integrate : Stream (Unsigned n) -> Stream (Unsigned n)
integrate xs = liftA2 (addWrap) xs (delay 0 $ integrate xs)

||| Boolean true every Rth cycle, starting at first cycle
everyR : (r: Nat) -> Stream Bool
everyR   Z    = pure False
everyR (S j) = map (\a=>modNatNZ a (S j) SIsNotZ == 0) $ counterFrom 0

||| Downsampler circuit
downsample : (r: Nat) -> Stream a -> Stream (Maybe a)
downsample r = zipWith (\e, x=>if e then Just x else Nothing) (everyR r)

||| Comb filter circuit
comb : (m : Nat) -> Stream (Maybe (Unsigned n)) -> Stream (Maybe (Unsigned n))
comb _ xs = map (\(a,b)=>map (`minusWrap` b) a) $
            zip xs (regMaybe 0 xs) -- TODO Delay by m... and get

--------------------------------------------------------------------------------
-- Wordlength calculations
--------------------------------------------------------------------------------

||| Recursive definition of a binomial coefficient
nChooseK : (n: Nat) -> (k: Nat) -> Nat
nChooseK n Z = 1
nChooseK Z (S k) = 0
nChooseK (S n) (S k) = if k>n then 0 else
                       nChooseK n k + nChooseK n (S k)

||| Helper to divide two `Nat`s safely, returning zero for division by zero
||| (fight me, mathematicians)
divNatOrZero : Nat -> Nat -> Nat
divNatOrZero k Z = Z
divNatOrZero k (S j) = divNatNZ k (S j) SIsNotZ

parameters (r, n, m : Nat)

  ||| Partial system function, $h_j(k)$ (Eq. 9b)
  hjk : (j, k : Nat) -> Integer
  hjk j k = case j <= n of
    True  => sum $ map (\l => pow (-1) l * cast (
                                (nChooseK n l) *
                                (nChooseK ((n `minus` j)+(k `minus` r*m*l)) (k `minus` r*m*l)))
                       ) [0..(divNatOrZero k (r*m))]
    False => pow (-1) k * cast (nChooseK (minus (2*n+1) j) k)

  ||| Variance error gain for stage j, $F(j)$ (Eq. 16b)
  fj : (j : Nat) -> Double
  fj j = case j == (2*n+1) of
      True  => 1.0
      False => sqrt . cast . sum $ map (\k=>pow (hjk j k) 2) [0..((r*m `minus` 1) * n + j `minus` 1)]

  ||| Max unpruned wordlength, $B_{max}$ (Eq 12)
  bmax : (bin : Nat) -> Nat
  bmax bin = bin + clog2 (pow (r*m) n)

  ||| Error at output due to final rounding/truncation, $E_{2N+1}$ (Eq. 12)
  eT2n1 : (bin, bout : Nat) -> Integer
  eT2n1 bin bout = pow 2 $ bmax bin `minus` bout

  ||| Variance at output due to final rounding/truncation, $\sigma_T_{2N+1}$ (Eq. 14)
  sigmaT2n1 : (bin, bout : Nat) -> Double
  sigmaT2n1 bin bout = sqrt $ cast (pow  (eT2n1 bin bout) 2) / 12.0

  ||| Bits to prune at stage j, $B_j$ (Eq. 21).
  ||| We use log laws to avoid errors with an integer implementation of log2
  bj : (bin, bout, j : Nat) -> Nat
  bj bin bout j = flog2Approx $ (sigmaT2n1 bin bout) * (sqrt $ 6.0 / (cast n)) / fj j

  ||| Bits to keep at stage j
  cicAccPruned : (bin, bout, j : Nat) -> Nat
  cicAccPruned bin bout j = if j==0 then bmax bin else
                                  if j>=(2*n+1) then bout else
                                  bmax bin `minus` bj bin bout j

--------------------------------------------------------------------------------
-- CIC decimator
--------------------------------------------------------------------------------

  ||| Recursive integrator chain
  partial --Because of integrate
  cicDecimateRecI : (bin, bout, j : Nat)
    -> Stream (Unsigned (cicAccPruned bin bout 0))
    -> Stream (Unsigned (cicAccPruned bin bout j))
  cicDecimateRecI bin bout  Z    = id
  cicDecimateRecI bin bout (S j) = map prune . integrate .
                                   cicDecimateRecI bin bout j

  ||| Recursive comb filter chain
  cicDecimateRecC : (bin, bout, j : Nat)
    -> Stream (Maybe (Unsigned (cicAccPruned bin bout n)))
    -> Stream (Maybe (Unsigned (cicAccPruned bin bout (j+n))))
  cicDecimateRecC bin bout  Z    = id
  cicDecimateRecC bin bout (S j) = map (map prune) . comb m .
                                   cicDecimateRecC bin bout j
  ||| CIC decimator circuit
  partial --Because of integrate
  cicDecimate : Stream (Unsigned bin) -> Stream (Maybe (Unsigned bout))
  cicDecimate {bin} {bout} =
    map (map prune) .                        -- Final truncation, after
    cicDecimateRecC bin bout n .             -- Recursive comb steps, after
    downsample r .                           -- Downsample, after
    cicDecimateRecI bin bout n .             -- Recursive integrate steps, after
    map (extend {m=cicAccPruned bin bout 0}) -- Input extend

-- TODO Is it worth proving that cicAccPruned bin bout (2*n+1)) == bout?

||| Example of calculating pruning for Hogenauer's design example (Section IV. D)
mainBj : IO ()
mainBj = print $ map (bj 25 4 1 16 16) [1..8]

||| Example of simulating `cicDecimate`
partial
mainSim : IO ()
mainSim = do let dut = cicDecimate {bin=8} {bout=8} 3 3 1
             let inp = map (\t=> saturate {n=8} . cast $
                                 sin (t*2*pi/10.0) * 127 + 127 )
                       $ counterFrom 0 {ty=Double}
             let out = take 40 $ simulate dut inp
             putStrLn . show $ zip (take 40 inp) out
