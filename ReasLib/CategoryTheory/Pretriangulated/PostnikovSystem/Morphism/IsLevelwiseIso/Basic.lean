module

public import ReasLib.CategoryTheory.Iso.Explicit
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Basic

/-!
# Levelwise Isomorphisms of Postnikov-System Morphisms

This file defines levelwise invertibility of the auxiliary-object components and exposes
their explicit isomorphisms. Stage-triangle and finite-row consequences live in separate
leaves.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- A morphism of Postnikov systems is levelwise invertible when each map on auxiliary objects is
an isomorphism. -/
@[stacks 0D83 "levelwise isomorphism of Postnikov systems"]
def IsLevelwiseIso {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} (ψ : PostnikovSystem.Morphism P P' φ) : Prop :=
  ∀ i : Fin (n + 1), IsIso (ψ.yMap i)

namespace IsLevelwiseIso

/-- A levelwise-isomorphism certificate makes each auxiliary-object component invertible. -/
theorem yMap {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (i : Fin (n + 1)) : IsIso (ψ.yMap i) := sorry

/-- The canonical isomorphism carried by an auxiliary-object component of a levelwise
isomorphism. -/
@[stacks 0D83 "component isomorphism of a levelwise Postnikov-system isomorphism"]
noncomputable def yIso {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (i : Fin (n + 1)) : P i ≅ P' i :=
  (hψ i).toIso

/-- The forward map of `yIso` is the corresponding auxiliary-object component. -/
@[simp, stacks 0D83]
theorem yIso_hom {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (i : Fin (n + 1)) :
    (hψ.yIso i).hom = ψ.yMap i := sorry

/-- The inverse map of `yIso` is the inverse selected by its explicit component
certificate. -/
@[simp, stacks 0D83]
theorem yIso_inv {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (i : Fin (n + 1)) :
    (hψ.yIso i).inv = (hψ i).toIso.inv := sorry

/-- An auxiliary-object component followed by the inverse of `yIso` is the identity. -/
@[simp, stacks 0D83]
theorem hom_inv_id {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (i : Fin (n + 1)) :
    ψ.yMap i ≫ (hψ.yIso i).inv = 𝟙 (P i) := sorry

/-- The inverse of `yIso` followed by its auxiliary-object component is the identity. -/
@[simp, stacks 0D83]
theorem inv_hom_id {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (i : Fin (n + 1)) :
    (hψ.yIso i).inv ≫ ψ.yMap i = 𝟙 (P' i) := sorry

end IsLevelwiseIso

end CategoryTheory.PostnikovSystem.Morphism
