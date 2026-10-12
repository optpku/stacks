/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem

/-!
# Presentations by Positive Adic Quotient Systems

This leaf records the concrete datum that a positive module inverse system is
identified stagewise with the powers-of-an-ideal quotient tower of one module.
It does not impose finiteness, grading, or a limiting property.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AdicCompletion.QuotientSystem

variable {R : Type u} [CommRing R]

/-- A positive inverse system presented by the positive adic quotient tower of
a single module. -/
structure Presentation
    (I : Ideal R) (F : PNatInverseSystem (ModuleCat.{v} R)) where
  /-- The module whose adic quotient tower presents `F`. -/
  object : ModuleCat.{v} R
  /-- The stagewise linear equivalence from the quotient tower of `object` to `F`. -/
  equiv : ∀ n : ℕ+,
    (object ⧸ I ^ (n : ℕ) • (⊤ : Submodule R object)) ≃ₗ[R] F.stage n
  /-- The stagewise equivalences commute with the successor transitions. -/
  step_comm : ∀ n : ℕ+,
    CommSq
      (AdicCompletion.positiveQuotientStepMap I object n)
      (ModuleCat.ofHom (equiv (n + 1)).toLinearMap)
      (ModuleCat.ofHom (equiv n).toLinearMap)
      (F.stepMap n)

end AdicCompletion.QuotientSystem
