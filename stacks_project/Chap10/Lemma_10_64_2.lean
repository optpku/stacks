/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import ReasLib.RingTheory.Ideal.SymbolicPower
import StacksCheckRecall

/-!
# Associated primes of symbolic-power quotients

@stack 0314
-/

@[expose] public section

@[stacks 0314 "positive symbolic powers are primary"]
#check @Ideal.symbolicPower_isPrimary

@[stacks 0314 "radical of a positive symbolic power"]
#check @Ideal.radical_symbolicPower

@[stacks 0314 "associated primes of a primary quotient"]
#check @associatedPrimes.eq_singleton_of_isPrimary
