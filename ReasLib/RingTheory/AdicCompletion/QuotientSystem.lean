/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Positive

/-!
# Positive Adic Quotient Systems

@stack 0318

This leaf packages the positive part of the canonical adic quotient tower.
The ambient inverse-system indexing implementation remains internal to this
definition; users work with `PNatInverseSystem.stage` and `stepMap`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- The quotient of `M` by the `n`th power of `I`, viewed as a module-category
object at a positive stage. -/
@[stacks 0318 "positive adic quotient stage"]
abbrev positiveQuotientStage (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ+) : ModuleCat.{v} R :=
  ModuleCat.of R (M ⧸ I ^ (n : ℕ) • (⊤ : Submodule R M))

/-- The positive inverse system `n ↦ M ⧸ I ^ n M` of adic quotient modules. -/
@[stacks 0318 "positive adic quotient inverse system"]
def positiveQuotientSystem (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    PNatInverseSystem (ModuleCat.{v} R) where
  obj i := positiveQuotientStage I M (OrderDual.ofDual i)
  map {i j} f := ModuleCat.ofHom <|
    AdicCompletion.transitionMap I M
      (show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
        show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
  map_id := by
    intro X
    ext x
    rfl
  map_comp := by
    intro X Y Z f g
    ext x
    rfl

/-- The stage facade for `positiveQuotientSystem` agrees with the explicit
positive quotient object. -/
@[stacks 0318 "positive quotient system stage", simp]
theorem positiveQuotientSystem_stage
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ+) :
    (positiveQuotientSystem I M).stage n = positiveQuotientStage I M n := sorry

/-- The successor transition in the positive adic quotient system. -/
@[stacks 0318 "positive adic quotient transition"]
abbrev positiveQuotientStepMap
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ+) :
    positiveQuotientStage I M (n + 1) ⟶ positiveQuotientStage I M n :=
  (positiveQuotientSystem I M).stepMap n

end AdicCompletion
