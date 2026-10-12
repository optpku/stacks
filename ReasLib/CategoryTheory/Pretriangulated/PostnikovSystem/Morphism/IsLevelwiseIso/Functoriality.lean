/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.IsLevelwiseIso.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Tail

/-!
# Functoriality of Levelwise Postnikov-System Isomorphisms

This file records preservation of levelwise invertibility under base transport,
composition, recursive tails, and identity morphisms.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism.IsLevelwiseIso

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Changing only the recorded base map of a levelwise isomorphism preserves levelwise
invertibility. -/
@[stacks 0D83]
theorem changeBase {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ φ' : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (h : φ = φ') :
    (PostnikovSystem.Morphism.changeBase h ψ).IsLevelwiseIso := sorry

/-- Changing the recorded base map preserves and reflects levelwise invertibility. -/
@[simp, stacks 0D83]
theorem changeBase_iff {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ φ' : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (h : φ = φ') :
    (PostnikovSystem.Morphism.changeBase h ψ).IsLevelwiseIso ↔ ψ.IsLevelwiseIso := sorry

/-- The component isomorphisms are unchanged when only the recorded base map is changed. -/
@[simp, stacks 0D83]
theorem changeBase_yIso {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ φ' : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (h : φ = φ') (i : Fin (n + 1)) :
    ((hψ.changeBase h).yIso i) = hψ.yIso i := sorry

/-- The composite of levelwise-isomorphic Postnikov-system morphisms is levelwise
isomorphic. -/
@[stacks 0D83]
theorem comp {n : ℕ} {X X' X'' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {P'' : PostnikovSystem X''} {φ : X ⟶ X'}
    {φ' : X' ⟶ X''} {ψ : PostnikovSystem.Morphism P P' φ}
    {χ : PostnikovSystem.Morphism P' P'' φ'} (hψ : ψ.IsLevelwiseIso)
    (hχ : χ.IsLevelwiseIso) :
    (PostnikovSystem.Morphism.comp ψ χ).IsLevelwiseIso := sorry

/-- Component isomorphisms of a composite are composites of the component isomorphisms. -/
@[simp, stacks 0D83]
theorem comp_yIso {n : ℕ} {X X' X'' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {P'' : PostnikovSystem X''} {φ : X ⟶ X'}
    {φ' : X' ⟶ X''} {ψ : PostnikovSystem.Morphism P P' φ}
    {χ : PostnikovSystem.Morphism P' P'' φ'} (hψ : ψ.IsLevelwiseIso)
    (hχ : χ.IsLevelwiseIso) (i : Fin (n + 1)) :
    ((hψ.comp hχ).yIso i) = (hψ.yIso i).trans (hχ.yIso i) := sorry

/-- Removing the first stage of a levelwise-isomorphic morphism preserves levelwise
invertibility. -/
@[stacks 0D83]
theorem tail {n : ℕ} {X X' : ComposableArrows D (n + 1)} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) :
    (PostnikovSystem.Morphism.tail ψ).IsLevelwiseIso := sorry

/-- A component isomorphism of the tail is the successor component isomorphism of the original
morphism. -/
@[simp, stacks 0D83]
theorem tail_yIso {n : ℕ} {X X' : ComposableArrows D (n + 1)} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (i : Fin (n + 1)) :
    (hψ.tail.yIso i) = hψ.yIso i.succ := sorry

/-- Any morphism between Postnikov systems over the identity row morphism is levelwise an
isomorphism. -/
@[stacks 0D83]
theorem of_identity {n : ℕ} {X : ComposableArrows D n} {P P' : PostnikovSystem X}
    (ψ : PostnikovSystem.Morphism P P' (𝟙 X)) :
    ψ.IsLevelwiseIso := sorry

/-- The identity morphism of a Postnikov system is levelwise isomorphic. -/
@[stacks 0D83]
theorem id {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) :
    (PostnikovSystem.Morphism.id P).IsLevelwiseIso := sorry

end CategoryTheory.PostnikovSystem.Morphism.IsLevelwiseIso
