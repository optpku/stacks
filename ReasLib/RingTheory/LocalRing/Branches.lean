/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization

/-!
# Branch numbers of local rings

This leaf owns the numerical branch invariants attached to a chosen
henselization or strict henselization of a local ring.  The relevant
minimal-prime set is kept explicit, so the definitions are independent of a
particular construction of either local algebra.
-/

@[expose] public section

universe u v

noncomputable section

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The branch number of `A` is the number of minimal primes of a chosen
henselization `Ah`. -/
@[stacks 0C26 "branch number"]
abbrev branchNumber
    (Ah : Type v) [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] : ℕ∞ :=
  (minimalPrimes Ah).encard

/-- The geometric branch number of `A` is the number of minimal primes of a
chosen strict henselization `Ash`. -/
@[stacks 0C26 "geometric branch number"]
abbrev geometricBranchNumber
    (Ash : Type v) [CommRing Ash] [Algebra A Ash]
    [IsStrictHenselizationOf A Ash] : ℕ∞ :=
  (minimalPrimes Ash).encard
