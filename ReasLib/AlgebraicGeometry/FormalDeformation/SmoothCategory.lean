/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic

/-!
# Smooth categories cofibered in groupoids

The absolute smoothness property of a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` and its lifting characterization.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type w} [Category.{v} F]

namespace CategoryTheory.Functor

/-- A category cofibered in groupoids is smooth when its structure morphism to the identity-based
category is a smooth based functor. -/
class IsSmooth (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] : Prop where
  /-- The structure morphism is smooth as a based functor. -/
  isSmooth_toBase :
    BasedFunctor.IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p))

/-- The identity functor on `ArtinianLocalAlgCat Λ k` is smooth. -/
instance instIsSmoothId : IsSmooth (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- Smoothness of a category cofibered in groupoids is smoothness of its structure morphism.
The converse is available explicitly through `isSmooth_iff`. -/
instance IsSmooth.spec (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    [h : IsSmooth p] :
    BasedFunctor.IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p)) :=
  h.isSmooth_toBase

/-- Smoothness supplies a lift along every surjection, with the over-`f` cell, the vertical over
`𝟙 B` cell, and triangle commutativity. -/
theorem IsSmooth.exists_lift (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    [IsSmooth p] {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) {y : ArtinianLocalAlgCat Λ k} {x : F}
    (α : y ⟶ p.obj x) (hα : (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift f α) :
    ∃ (x' : F) (β : x' ⟶ x) (γ : p.obj x' ⟶ y),
      p.IsHomLift f β ∧ (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift (𝟙 B) γ ∧
        γ ≫ α = p.map β := sorry

/-- Unobstructedness is a reducible synonym for smoothness, as in Stacks tag 06HP. -/
abbrev IsUnobstructed (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    Prop :=
  IsSmooth p

/-- Smoothness of a category cofibered in groupoids is smoothness of its structure morphism. -/
theorem isSmooth_iff (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    IsSmooth p ↔
      BasedFunctor.IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p)) :=
  ⟨fun h ↦ h.isSmooth_toBase, fun h ↦ ⟨h⟩⟩

end CategoryTheory.Functor
