/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite-Type Field Algebras after Localization

@stack 00FY

A finite-type embedding into a field becomes a finite field extension after localizing the source
at one nonzero element.
-/

universe u v

namespace Algebra.FiniteType

/-- Lemma 10.34.2: if `R` embeds into a field `K` which is finite type over `R`, then some
nonzero away localization of `R` is a field and its canonical map to `K` is finite. -/
@[stacks 00FY]
theorem exists_away_isField_and_finite
    {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K]
    [Algebra.FiniteType R K] (hinj : Function.Injective (algebraMap R K)) :
    ∃ (f : R) (hf : f ≠ 0),
      IsField (Localization.Away f) ∧
        RingHom.Finite
          (Localization.awayLift (algebraMap R K) f
            (IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R K) hinj).2 hf))) := sorry

end Algebra.FiniteType
