module Synchronous

import Data.Vect

%access export
%default total

counterFrom : Num ty => ty -> Stream ty
counterFrom = iterate (+1)

simulate : (Stream a -> Stream b) -> Stream a -> Stream b
simulate f xs = f xs

public export
delay : a -> Stream a -> Stream a
delay a s = a :: s

mux : Stream Bool -> Stream a -> Stream a -> Stream a
mux = liftA3 (\e,a,b=>if e then a else b)

regEn : a -> Stream Bool -> Stream a -> Stream a
regEn a (False :: xs) (y :: ys) = a :: regEn a xs ys
regEn a (True  :: xs) (y :: ys) = a :: regEn y xs ys

regMaybe : a -> Stream (Maybe a) -> Stream a
regMaybe a (Nothing  :: xs) = a :: regMaybe a xs
regMaybe a ((Just x) :: xs) = a :: regMaybe x xs

public export
window : (n : Nat) -> a -> Stream a -> Stream (Vect n a)
window Z a xs     = pure []
window (S k) a xs = let dl = scanl (flip delay) xs (replicate (k) a)
                    in  sequence dl

