module

public import ReasLib.CategoryTheory.Adjunction.Derived.Total.Basic

@[expose] public section

/-!
# Naturality of Total Pointwise-Derived Hom-Equivalences

The canonical total Hom-equivalence is natural in both variables, in both forward and inverse
directions.
-/

open CategoryTheory
open CategoryTheory.MorphismProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction.Total

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  {F : D ⥤ D'} {G : D' ⥤ D}

/-- Naturality of the total pointwise-derived Hom-equivalence in the left-derived variable. -/
@[reassoc, stacks 09T5]
theorem homEquiv_naturality_left
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    {K : S.Localization} {M₁ M₂ : S'.Localization}
    (m : M₁ ⟶ M₂)
    (f : ((G ⋙ S.Q).totalLeftDerived S'.Q S').obj M₂ ⟶ K) :
    homEquiv adj S S' K M₁
        (((G ⋙ S.Q).totalLeftDerived S'.Q S').map m ≫ f) =
      m ≫ homEquiv adj S S' K M₂ f := sorry

/-- Naturality of the total pointwise-derived Hom-equivalence in the right-derived variable. -/
@[reassoc, stacks 09T5]
theorem homEquiv_naturality_right
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    {K₁ K₂ : S.Localization} {M : S'.Localization}
    (k : K₁ ⟶ K₂)
    (f : ((G ⋙ S.Q).totalLeftDerived S'.Q S').obj M ⟶ K₁) :
    homEquiv adj S S' K₂ M (f ≫ k) =
      homEquiv adj S S' K₁ M f ≫
        ((F ⋙ S'.Q).totalRightDerived S.Q S).map k := sorry

/-- Naturality of the inverse total Hom-equivalence in the left-derived variable. -/
@[reassoc, stacks 09T5]
theorem homEquiv_naturality_left_symm
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    {K : S.Localization} {M₁ M₂ : S'.Localization}
    (m : M₁ ⟶ M₂)
    (f : M₂ ⟶ ((F ⋙ S'.Q).totalRightDerived S.Q S).obj K) :
    (homEquiv adj S S' K M₁).symm (m ≫ f) =
      ((G ⋙ S.Q).totalLeftDerived S'.Q S').map m ≫
        (homEquiv adj S S' K M₂).symm f := sorry

/-- Naturality of the inverse total Hom-equivalence in the right-derived variable. -/
@[reassoc, stacks 09T5]
theorem homEquiv_naturality_right_symm
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    {K₁ K₂ : S.Localization} {M : S'.Localization}
    (k : K₁ ⟶ K₂)
    (f : M ⟶ ((F ⋙ S'.Q).totalRightDerived S.Q S).obj K₁) :
    (homEquiv adj S S' K₂ M).symm
        (f ≫ ((F ⋙ S'.Q).totalRightDerived S.Q S).map k) =
      (homEquiv adj S S' K₁ M).symm f ≫ k := sorry

end CategoryTheory.Adjunction.Total
