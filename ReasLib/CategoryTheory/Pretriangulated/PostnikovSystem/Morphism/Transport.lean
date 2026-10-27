/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Basic

@[expose] public section

/-!
# Transport of Postnikov-System Morphisms

This leaf transports a Postnikov-system morphism along an equality of its
underlying finite-row map, independently of any particular construction.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {n : ℕ} {X X' : ComposableArrows D n}
variable {P : PostnikovSystem X} {P' : PostnikovSystem X'} {φ : X ⟶ X'}

/-- Transport a Postnikov-system morphism along an equality of its underlying row map. -/
@[stacks 0D7Z "transport of a Postnikov-system morphism over its base map"]
def changeBase {φ' : X ⟶ X'} (h : φ = φ')
    (ψ : PostnikovSystem.Morphism P P' φ) :
    PostnikovSystem.Morphism P P' φ' :=
  h ▸ ψ

/-- Transport along reflexivity does not change a Postnikov-system morphism. -/
@[simp, stacks 0D7Z]
theorem changeBase_rfl (ψ : PostnikovSystem.Morphism P P' φ) :
    changeBase rfl ψ = ψ := rfl

/-- Successive transports of a Postnikov-system morphism combine by transitivity. -/
@[stacks 0D7Z]
theorem changeBase_trans {φ' φ'' : X ⟶ X'} (h : φ = φ') (h' : φ' = φ'')
    (ψ : PostnikovSystem.Morphism P P' φ) :
    changeBase h' (changeBase h ψ) = changeBase (h.trans h') ψ := by
  cases h
  cases h'
  rfl

/-- Transporting a Postnikov-system morphism and then transporting back along the
reverse equality recovers the original morphism. -/
@[simp, stacks 0D7Z]
theorem changeBase_symm_apply {φ' : X ⟶ X'} (h : φ = φ')
    (ψ : PostnikovSystem.Morphism P P' φ) :
    changeBase h.symm (changeBase h ψ) = ψ := by
  cases h
  rfl

/-- Transporting back along an equality and then forward again recovers the original
Postnikov-system morphism. -/
@[simp, stacks 0D7Z]
theorem changeBase_apply_symm {φ' : X ⟶ X'} (h : φ = φ')
    (ψ : PostnikovSystem.Morphism P P' φ') :
    changeBase h (changeBase h.symm ψ) = ψ := by
  cases h
  rfl

/-- Equality of underlying row maps induces an equivalence between the corresponding fibers of
Postnikov-system morphisms. -/
@[stacks 0D7Z]
def changeBaseEquiv {φ' : X ⟶ X'} (h : φ = φ') :
    PostnikovSystem.Morphism P P' φ ≃ PostnikovSystem.Morphism P P' φ' where
  toFun := changeBase h
  invFun := changeBase h.symm
  left_inv := changeBase_symm_apply h
  right_inv := changeBase_apply_symm h

/-- The forward map of `changeBaseEquiv` is transport along the supplied base-map equality. -/
@[simp, stacks 0D7Z]
theorem changeBaseEquiv_apply {φ' : X ⟶ X'} (h : φ = φ')
    (ψ : PostnikovSystem.Morphism P P' φ) :
    changeBaseEquiv h ψ = changeBase h ψ := rfl

/-- The inverse map of `changeBaseEquiv` is transport along the reverse base-map equality. -/
@[simp, stacks 0D7Z]
theorem changeBaseEquiv_symm_apply {φ' : X ⟶ X'} (h : φ = φ')
    (ψ : PostnikovSystem.Morphism P P' φ') :
    (changeBaseEquiv h).symm ψ = changeBase h.symm ψ := rfl

/-- Transport along an equality of base maps is injective on Postnikov-system morphisms. -/
@[stacks 0D7Z]
theorem changeBase_injective {φ' : X ⟶ X'} (h : φ = φ') :
    Function.Injective (changeBase (P := P) (P' := P') h) :=
  (changeBaseEquiv (P := P) (P' := P') h).injective

/-- Two Postnikov-system morphisms become equal after the same base-map transport exactly
when they were already equal. -/
@[simp, stacks 0D7Z]
theorem changeBase_eq_iff {φ' : X ⟶ X'} (h : φ = φ')
    (ψ χ : PostnikovSystem.Morphism P P' φ) :
    changeBase h ψ = changeBase h χ ↔ ψ = χ :=
  (changeBase_injective h).eq_iff

/-- Transporting the base map leaves every auxiliary-object component unchanged. -/
@[simp, stacks 0D7Z]
theorem changeBase_yMap {φ' : X ⟶ X'} (h : φ = φ')
    (ψ : PostnikovSystem.Morphism P P' φ) (i : Fin (n + 1)) :
    (changeBase h ψ).yMap i = ψ.yMap i := by
  cases h
  rfl

/-- A transported Postnikov-system morphism equals a morphism over the new base map exactly when
their auxiliary-object components agree. -/
@[simp, stacks 0D7Z]
theorem changeBase_eq_iff_yMap {φ' : X ⟶ X'} (h : φ = φ')
    (ψ : PostnikovSystem.Morphism P P' φ) (χ : PostnikovSystem.Morphism P P' φ') :
    changeBase h ψ = χ ↔ ∀ i, ψ.yMap i = χ.yMap i := by
  cases h
  constructor
  · intro e i
    exact congrArg (fun ξ : PostnikovSystem.Morphism P P' φ ↦ ξ.yMap i) e
  · intro e
    cases ψ with
    | mk yMap h₁ h₂ h₃ =>
      cases χ with
      | mk yMap' h₁' h₂' h₃' =>
        have hy : yMap = yMap' := funext e
        cases hy
        rfl

end CategoryTheory.PostnikovSystem.Morphism
