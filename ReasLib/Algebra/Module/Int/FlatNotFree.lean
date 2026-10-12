/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Int.PrimeDirectSum
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

noncomputable section

namespace Int

/-- The localization of `ℤ` at the prime ideal `(2)`. -/
abbrev localizationAtTwo : Type :=
  PrimeDirectSum.atPrime ⟨2, Nat.prime_two⟩

/-- The fraction ring of the localization of `ℤ` at `(2)` is flat over that localization. -/
instance fractionRing_flat :
    Module.Flat localizationAtTwo (FractionRing localizationAtTwo) :=
  IsLocalization.flat _ (nonZeroDivisors _)

/-- The fraction ring of the localization of `ℤ` at `(2)` is not free over that localization. -/
theorem fractionRing_not_free :
    ¬ Module.Free localizationAtTwo (FractionRing localizationAtTwo) := sorry

end Int
