/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Morphism Properties Compatible with Triangulations

This leaf relates the one-shift and triangle-completion presentation of a
triangulation-compatible morphism property to mathlib's canonical classes.
-/

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Pretriangulated.Opposite

universe v u

namespace CategoryTheory.MorphismProperty.Triangulated

section Shift

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- Invariance under the shift by `1` propagates to every integer shift once the property
respects isomorphisms. -/
theorem mem_shift_iff_of_one
    (S : MorphismProperty D) [S.RespectsIso]
    (h_one : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), S (f⟦(1 : ℤ)⟧') ↔ S f)
    {X Y : D} (f : X ⟶ Y) (n : ℤ) :
    S (f⟦n⟧') ↔ S f := sorry

end Shift

section Completion

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (S : MorphismProperty D)

/-- Triangle completion and identity membership force every isomorphism to belong to the
morphism property. -/
@[stacks 05R3]
theorem isomorphisms_le [S.ContainsIdentities]
    (h_complete :
      ∀ (T₁ T₂ : Triangle D) (_ : T₁ ∈ distTriang D) (_ : T₂ ∈ distTriang D)
        (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
          S a → S b → T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
            ∃ c : T₁.obj₃ ⟶ T₂.obj₃, S c ∧
              T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
                T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃) :
    isomorphisms D ≤ S := sorry

/-- Stacks 0H30: one-shift invariance and triangle completion assemble the canonical
triangulation-compatibility instance. -/
@[stacks 0H30]
theorem of_one [S.IsMultiplicative]
    (h_complete :
      ∀ (T₁ T₂ : Triangle D) (_ : T₁ ∈ distTriang D) (_ : T₂ ∈ distTriang D)
        (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
          S a → S b → T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
            ∃ c : T₁.obj₃ ⟶ T₂.obj₃, S c ∧
              T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
                T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃)
    (h_one : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), S (f⟦(1 : ℤ)⟧') ↔ S f) :
    S.IsCompatibleWithTriangulation := sorry

/-- With triangle completion fixed, one-shift invariance is equivalent to the canonical
all-shifts compatibility class. -/
theorem one_iff_compatibleShift [S.IsMultiplicative]
    (h_complete :
      ∀ (T₁ T₂ : Triangle D) (_ : T₁ ∈ distTriang D) (_ : T₂ ∈ distTriang D)
        (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
          S a → S b → T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
            ∃ c : T₁.obj₃ ⟶ T₂.obj₃, S c ∧
              T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
                T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃) :
    (∀ ⦃X Y : D⦄ (f : X ⟶ Y), S (f⟦(1 : ℤ)⟧') ↔ S f) ↔
      S.IsCompatibleWithShift ℤ := sorry

/-- With triangle completion fixed, invariance under the shift by `1` is equivalent to
invariance under every integer shift. -/
theorem one_iff_all [S.IsMultiplicative]
    (h_complete :
      ∀ (T₁ T₂ : Triangle D) (_ : T₁ ∈ distTriang D) (_ : T₂ ∈ distTriang D)
        (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
          S a → S b → T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
            ∃ c : T₁.obj₃ ⟶ T₂.obj₃, S c ∧
              T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
                T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃) :
    (∀ ⦃X Y : D⦄ (f : X ⟶ Y), S (f⟦(1 : ℤ)⟧') ↔ S f) ↔
      ∀ ⦃X Y : D⦄ (f : X ⟶ Y) (n : ℤ), S (f⟦n⟧') ↔ S f := sorry

end Completion

section Opposite

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Triangulation compatibility is preserved by passing to the opposite morphism property. -/
noncomputable instance op (S : MorphismProperty D)
    [S.IsMultiplicative] [S.IsCompatibleWithTriangulation] :
    S.op.IsCompatibleWithTriangulation := sorry

end Opposite

end CategoryTheory.MorphismProperty.Triangulated
