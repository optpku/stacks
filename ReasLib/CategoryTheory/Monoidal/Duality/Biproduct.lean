/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Duality and binary biproducts

Binary biproducts of explicit exact pairings are exact pairings.  The construction records the
diagonal coevaluation and evaluation maps directly; no adjunction or chosen comparison
isomorphism is part of the public data.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
variable [HasBinaryBiproducts C]

namespace ExactPairing

/-- The componentwise exact pairing on binary biproducts. -/
@[stacks 0FFT, implicit_reducible]
noncomputable def biprod [MonoidalPreadditive C] {X₁ Y₁ X₂ Y₂ : C}
    (p₁ : ExactPairing X₁ Y₁) (p₂ : ExactPairing X₂ Y₂) :
    ExactPairing (X₁ ⊞ X₂) (Y₁ ⊞ Y₂) where
  coevaluation' :=
    p₁.coevaluation' ≫
        ((biprod.inl : X₁ ⟶ X₁ ⊞ X₂) ⊗ₘ (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂)) +
      p₂.coevaluation' ≫
        ((biprod.inr : X₂ ⟶ X₁ ⊞ X₂) ⊗ₘ (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂))
  evaluation' :=
    ((biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁) ⊗ₘ (biprod.fst : X₁ ⊞ X₂ ⟶ X₁)) ≫
        p₁.evaluation' +
      ((biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂) ⊗ₘ (biprod.snd : X₁ ⊞ X₂ ⟶ X₂)) ≫
        p₂.evaluation'
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- The coevaluation of the componentwise biproduct pairing is the sum of its two diagonal
components. -/
theorem biprod_coevaluation' [MonoidalPreadditive C] {X₁ Y₁ X₂ Y₂ : C}
    (p₁ : ExactPairing X₁ Y₁) (p₂ : ExactPairing X₂ Y₂) :
    (p₁.biprod p₂).coevaluation' =
      p₁.coevaluation' ≫
          ((biprod.inl : X₁ ⟶ X₁ ⊞ X₂) ⊗ₘ (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂)) +
        p₂.coevaluation' ≫
          ((biprod.inr : X₂ ⟶ X₁ ⊞ X₂) ⊗ₘ (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂)) := sorry

/-- The evaluation of the componentwise biproduct pairing is the sum of its two diagonal
components. -/
theorem biprod_evaluation' [MonoidalPreadditive C] {X₁ Y₁ X₂ Y₂ : C}
    (p₁ : ExactPairing X₁ Y₁) (p₂ : ExactPairing X₂ Y₂) :
    (p₁.biprod p₂).evaluation' =
      ((biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁) ⊗ₘ (biprod.fst : X₁ ⊞ X₂ ⟶ X₁)) ≫
          p₁.evaluation' +
        ((biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂) ⊗ₘ (biprod.snd : X₁ ⊞ X₂ ⟶ X₂)) ≫
          p₂.evaluation' := sorry

/-- Typeclass search uses the componentwise pairing on binary biproducts. -/
@[implicit_reducible]
noncomputable instance instBiprod [MonoidalPreadditive C] {X₁ Y₁ X₂ Y₂ : C}
    [p₁ : ExactPairing X₁ Y₁] [p₂ : ExactPairing X₂ Y₂] :
    ExactPairing (X₁ ⊞ X₂) (Y₁ ⊞ Y₂) :=
  p₁.biprod p₂

end ExactPairing

namespace HasLeftDual

/-- A binary biproduct of left-dualizable objects is left dualizable, with the binary biproduct
of the chosen left duals as its chosen left dual. -/
@[implicit_reducible]
noncomputable instance biprod [MonoidalPreadditive C]
    {X Y : C} [HasLeftDual X] [HasLeftDual Y] :
    HasLeftDual (X ⊞ Y) where
  leftDual := (ᘁX : C) ⊞ (ᘁY : C)
  exact := ExactPairing.biprod
    (inferInstanceAs (ExactPairing (ᘁX : C) X))
    (inferInstanceAs (ExactPairing (ᘁY : C) Y))

end HasLeftDual

namespace HasRightDual

/-- A binary biproduct of right-dualizable objects is right dualizable, with the binary biproduct
of the chosen right duals as its chosen right dual. -/
@[implicit_reducible]
noncomputable instance biprod [MonoidalPreadditive C]
    {X Y : C} [HasRightDual X] [HasRightDual Y] :
    HasRightDual (X ⊞ Y) where
  rightDual := (Xᘁ : C) ⊞ (Yᘁ : C)
  exact := ExactPairing.biprod
    (inferInstanceAs (ExactPairing X (Xᘁ : C)))
    (inferInstanceAs (ExactPairing Y (Yᘁ : C)))

end HasRightDual

end CategoryTheory
