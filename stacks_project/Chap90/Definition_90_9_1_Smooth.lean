module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap90.Definition_90_8_1_Smooth

/-!
# Smooth or unobstructed categories cofibered in groupoids

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is smooth, or
unobstructed, when its structure morphism is a smooth morphism of categories
cofibered in groupoids.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type w} [Category.{v} F]

namespace CategoryTheory.Functor

/-- The identity functor on `ArtinianLocalAlgCat Λ k` is cofibered in groupoids after
passing to opposite categories. -/
instance instIsFiberedInGroupoidsIdOp :
    IsFibered.InGroupoids (𝟭 (ArtinianLocalAlgCat Λ k)).op := sorry

/-- A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is smooth if its
structure morphism is a smooth morphism of categories cofibered in groupoids. -/
class IsSmooth (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] : Prop where
  /-- The structure morphism `BasedCategory.toBase (BasedCategory.ofFunctor p)` is
  smooth in the sense of Definition 90.8.1. -/
  isSmooth_toBase :
    BasedFunctor.IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p))

/-- The identity functor on `ArtinianLocalAlgCat Λ k` is a smooth category cofibered in
groupoids. -/
instance instIsSmoothId : IsSmooth (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- Smoothness of a category cofibered in groupoids is smoothness of its structure
morphism. -/
instance IsSmooth.spec (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    [h : IsSmooth p] :
    BasedFunctor.IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p)) :=
  h.isSmooth_toBase

/-- A category cofibered in groupoids is smooth as soon as its structure morphism is
smooth. -/
instance instIsSmooth.of_toBase (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op]
    [h : BasedFunctor.IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p))] :
    IsSmooth p where
  isSmooth_toBase := h

/-- Smoothness of the structure morphism supplies a lift along every surjection, with the
over-`f` cell, the vertical over-`𝟙 B` cell, and triangle commutativity. -/
theorem IsSmooth.exists_lift (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    [IsSmooth p] {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) {y : ArtinianLocalAlgCat Λ k} {x : F}
    (α : y ⟶ p.obj x) (hα : (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift f α) :
    ∃ (x' : F) (β : x' ⟶ x) (γ : p.obj x' ⟶ y),
      p.IsHomLift f β ∧ (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift (𝟙 B) γ ∧
        γ ≫ α = p.map β := sorry

/-- Unobstructed is a synonym for smooth for a category cofibered in groupoids. -/
abbrev IsUnobstructed (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    Prop :=
  IsSmooth p

/-- Unobstructedness is equivalent to smoothness. -/
theorem isUnobstructed_iff (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] : IsUnobstructed p ↔ IsSmooth p := sorry

end CategoryTheory.Functor
