# Playing with Dependent Types for Minimal Bit Growth

I'm playing about with dependent types as they apply to describing DSP hardware.
Here I'll go from nothing to an FIR filter that uses minimal bit growth, as
informed by the (static) values of its coefficients. All of this is enforced in
the types, so there's no scope for undetected user error in its use.


## Describing unsigned binary numbers

First of all, let's make a wee implementation of unsigned, fixed bit-width
numbers. This is just meant to be a stand-in for the Unsigned type in Clash.

> data Unsigned : (n : Nat) -> Type where
>   U : Integer -> Unsigned n
>
> toInteger : Unsigned n -> Integer
> toInteger (U x) = x
>
> Eq (Unsigned n) where
>   (==) (U x) (U y) = x==y
>
> Ord (Unsigned n) where
>  compare (U x) (U y) = compare x y
>
> MinBound (Unsigned n) where
>   minBound = U 0
>
> MaxBound (Unsigned n) where
>   maxBound = U $ cast (power 2 n)-1
>
> saturate : Unsigned n -> Unsigned n
> saturate (U x) = if U {n} x > maxBound then maxBound else
>                  if U {n} x < minBound then minBound else U x
>
> Num (Unsigned n) where
>   (+) (U x) (U y) = saturate $ U (x+y)
>   (*) (U x) (U y) = saturate $ U (x*y)
>   fromInteger x   = saturate $ U x
>
> Show (Unsigned n) where
>   show (U x) = "U" ++ show n ++ " " ++ show x

If we were actually going to use this, we'd want to consider constraining the
constructor, `U`, to only accept Integers that are representable by n bits.


## Using types to track the range of an number

OK. Now let's think about how we track a number's range in its type. For
unsigned numbers, we can _could_ re-use the `Fin` type. `Fin` is a type for
finite sets, and `Fin n` is the type inhabited by all integers from 0 through
(n-1). However, there are two good reasons why we'll make our own instead:

  * We will want to support signed and fixed-point numbers eventually. While
    these can be expressed as finite sets too, the meaning is a little trickier
    to work with... Is zero actually zero, or the minimum value?

  * More importantly, `Fin` is defined recursively, just like the Peano numbers
    used in Nat. This has huge implications for performance. Idris knows about
    the relationship between Peano numerals and their integer meaning, so can
    still make use of our PC's integer arithmetic. Idris will not do the same
    for `Fin`. The comments in Fin.idr says as much: "It's probably not a good
    idea to use `Fin` for arithmetic, and they will be exceedingly inefficient
    at run time."

Jeepers. Let's not use `Fin` then.

Let's call our type `UBounded`, short for "Unsigned Bounded". How about just
using a `Nat` to track the maximum value the type should hold. Here `UBounded n`
should be able to represent all integers from 0 through n, making the type-level
arithmetic a little simpler than with the case with `Fin`.

> data UBounded : (n: Nat) -> Type where
>   UB :  (n:Nat) -> (m:Nat) -> UBounded m

TODO: Consider enforcing n<=m in the constructor type here.

We'll need to be able to convert between `Unsigned` and `UBounded`. So, let's
think about how we convert between bit widths and integer ranges. We'll need to
make our own function for the ceiling of log base 2, based on the Prelude's
`log2` function for `Nats`.

> clog2B : Nat -> Nat
> clog2B Z = 0
> clog2B (S Z) = 0
> clog2B (S (S n)) = let y1 = log2NZ (S (S n)) SIsNotZ
>                        y2 = log2NZ (S n) SIsNotZ in
>                    if y1 == y2 then y1+1 else y1

> maxToBits : Nat -> Nat
> maxToBits = clog2B . (+1)

> bitsToMax : Nat -> Nat
> bitsToMax = Nat.pred . power 2

> fromUnsigned : Unsigned n -> UBounded (bitsToMax n)
> fromUnsigned {n} x = UB (fromInteger $ toInteger x) (bitsToMax n)

> toUnsigned : UBounded n -> Unsigned (maxToBits n)
> toUnsigned (UB x _) = U (cast x)

> zeros : UBounded n
> zeros = UB 0 n

OK, now look at how we define arithmetic for `UBounded`, using dependent types
to track the new maximum value.

> addUB : UBounded n ->UBounded m -> UBounded (n+m)
> addUB (UB x n) (UB y m) = UB (x+y) (n+m)

> multUB : UBounded n ->UBounded m -> UBounded (n*m)
> multUB (UB x n) (UB y m) = UB (x*y) (n*m)

> constAddUB : UBounded n -> (m: Nat) -> UBounded (n+m)
> constAddUB (UB x n) m = UB (x+m) (n+m)

> constMultUB : UBounded n -> (m: Nat) -> UBounded (n*m)
> constMultUB (UB x n) m = UB (x*m) (n*m)

We could easily go from here to a `Num` instance too. Let's just take a moment
to look at how neat this is compared to the implementation we had in Clash:

< addS :: forall n m a . (KnownNat m, KnownNat a, KnownNat n)
<       => ScaledWord n (m+1) -> ScaledWord n (1+a) -> ScaledWord n (m+a+2)
< addS a b = fromU' u (addSNat m' a')
<   where u  = resize $ add (toU a) (toU b)
<         m' = addSNat d1 . snatProxy $ Proxy @ m
<         a' = addSNat d1 . snatProxy $ Proxy @ a
<
< constMultS :: forall n m a . (KnownNat m, KnownNat a, KnownNat n)
<             => ScaledWord n (1+m) -> SNat (1+a) -> ScaledWord n ((1+m)*(1+a))
< constMultS a nat = fromU' u (mulSNat m' nat)
<   where u  = (snatToNum nat) * (resize (toU a))
<         m' = addSNat d1 . snatProxy $ Proxy @ m

🤮


## A dependently typed FIR filter

Great, so how do we use `UBounded` to get from a `List Nat` of coeffs to a
minimal FIR filter? Our accumulated value needs dependent types, so it would be
difficult to use the standard `fold`s. However, we *can* implement this
recursively, along this lines of `fir (w::ws) x = x*w + fir ws x`.

If you try that right off the bat, Idris will ask us to prove that the types
really line up. We show the proof up-front, but it was written after the `fir`
function while in conversation with the interpreter.

> firProof : (n : Nat) -> (w: Nat) -> (ws : List Nat) ->
>            UBounded (n * (w + sum ws)) = UBounded (n * w + n * sum ws)
> firProof n w ws = rewrite multDistributesOverPlusRight n w (sum ws) in Refl

> fir : (ws : List Nat) -> UBounded n -> UBounded (n * sum ws)
> fir [] x = zeros
> fir {n} (w :: ws) x = let result = addUB (constMultUB x w) (fir ws x) in
>                       rewrite firProof n w ws in result

I was surprised that Idris needed no help to prove that `w + sum ws = sum
(w::ws)`! Pretty neat. We only needed to remind it of multiplication's
distributive property.

We can expose a "hardware friendly" version of this function by converting the
`UBounded` arguments to `Unsigned`.

> firU : (ws : List Nat) -> Unsigned n -> Unsigned (maxToBits $ (bitsToMax n) * (sum ws))
> firU ws x = toUnsigned . fir ws $ fromUnsigned x


## Using our FIR implementation

Great! We have an implementation of an FIR now, but let's think about how
someone would use it. Ideally the bit-widths would be discoverable --- i.e. the
user defines the weights and the input bit-width, then just asks the REPL what
the output bit-width should be. In the simplest case, this is exactly what we
could do! Try supplying arguments to `firU` and then asking the REPL what the
type of the expression is:

```
Idris> :t firU [3,5,10,6,3] (U 0 {n=8})
firU [3, 5, 10, 6, 3] (U 0) : Unsigned 13
```

In less trivial situations the REPL may choose not to fully normalise the output
type. If that's the case, we can use `Elab` (often used for interactive theorem
proving) to force normalisation. First, define an FIR with weights specified and
holes where necessary to avoid specifying the output type.

> firDisco : Unsigned 5 -> ?out_type
> firDisco x = let y = firU [1, 1, 1, 1] x in ?out_value

Not we can inspect the holes and ask `Elab` to do some normalisation.
TODO: Check if we can use :exec from the repl instead.

```
*DependentBitWidth> :elab out_value


----------                 Goal:                  ----------
{hole_0} : Unsigned (fromInteger 5) ->
           Unsigned (maxToBits (bitsToMax (fromInteger 5) *
                                sum [fromInteger 1,
                                     fromInteger 1,
                                     fromInteger 1,
                                     fromInteger 1])) ->
           ?out_type
-Main.out_value> compute


----------                 Goal:                  ----------
{hole_0} : Unsigned 5 -> Unsigned 7 -> ?out_type
-Main.out_value> :abandon
Abandoned
```

From this, we can see that the output should be `Unsigned 7`. We can replace the
hole `?out_type` with this, and remove the `let` binding from the body.

Cheers,
Craig


> main : IO ()
> main = do putStrLn . show $ firU [3,5,4,1] (U 10 {n=8})


## Errata

NOTE: Think about whether it's a good idea or not to abstract the clog2 and
      power 2... Types look neater but hides the intent a bit.

NOTE: Also, what the fuck is going on with the run-time of this?! It's taking an
      age to generate 4 weight filters with firU at the REPL...

NOTE: Think about using a Stream like data type to encode the delay function
