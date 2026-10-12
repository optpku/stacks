/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.137.10 compatibility entry point

`Algebra.SmoothAtPrime` and its finitely presented comparison are maintained
by `ReasLib.RingTheory.Smooth.AtPrime`.

@stack 00TB
-/

/- Definition 10.137.10: an `R`-algebra `S` is smooth at `q : PrimeSpectrum S` when some
basic open neighbourhood of `q` is smooth over `R`. -/
@[stacks 00TB]
#check @Algebra.SmoothAtPrime
@[stacks 00TB "basic-open characterization"]
#check @Algebra.SmoothAtPrime.iff_exists_away
