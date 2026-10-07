module

public import stacks_project.Chap90.Definition_90_3_2_SmallExtension
public import stacks_project.Chap90.Definition_90_8_1_Smooth

/-!
# Smoothness from small-extension lifts

A morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is
smooth as soon as the infinitesimal lifting property holds along small extensions.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)

universe u v w v' w'

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/-- Lemma 90.8.2: a morphism `φ` of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is smooth if the infinitesimal lifting property of
Definition 90.8.1 is assumed only along small extensions `B ⟶ A`. -/
@[stacks 06HH]
theorem isSmooth_of_exists_lift_isSmallExtension
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y)
    (h : ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
      {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x), Y.p.IsHomLift f α →
        ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
          X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β) :
    IsSmooth φ := sorry

/-- Smoothness of a morphism of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is equivalent to the infinitesimal lifting property
along small extensions. -/
theorem isSmooth_iff_exists_lift_isSmallExtension
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y) :
    IsSmooth φ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x), Y.p.IsHomLift f α →
          ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
            X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β := sorry

/-- Smoothness supplies a lift along every small extension, with the over-`f` cell,
the vertical over-`𝟙 B` cell, and triangle commutativity. -/
theorem IsSmooth.exists_lift_isSmallExtension
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y) [IsSmooth φ] {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    [IsSmallExtension f] {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x)
    (hα : Y.p.IsHomLift f α) :
    ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
      X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β := sorry

end CategoryTheory.BasedFunctor
