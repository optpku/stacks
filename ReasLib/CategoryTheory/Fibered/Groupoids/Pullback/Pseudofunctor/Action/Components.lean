module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor.Action.Underlying

/-!
# Component computations for fixed-base pullback in groupoids

This leaf exposes the componentwise action, naturality, and vertical-composition laws of pulled
back groupoid-fibred `2`-cells.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

open CategoryTheory Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- A component of a pulled-back groupoid-fibred `2`-morphism is the neutral pullback component. -/
@[simp]
theorem map₂.app
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    (x : CategoricalPullback u ((FiberedCategoryOver.Groupoids.toFibered D).obj X).p) :
    (map₂ u eta).hom.toNatTrans.app x =
      FiberedCategoryOver.Pullback.mapApp u
        ((FiberedCategoryOver.Groupoids.toFibered D).map₂ eta) x := sorry

/-- The base component of a pulled-back groupoid-fibred `2`-morphism is the identity. -/
@[simp]
theorem map₂.app.fst
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    (x : CategoricalPullback u ((FiberedCategoryOver.Groupoids.toFibered D).obj X).p) :
    ((map₂ u eta).hom.toNatTrans.app x).fst = 𝟙 x.fst := sorry

/-- The total-category component of a pulled-back groupoid-fibred `2`-morphism is the original
vertical component on the second pullback coordinate. -/
@[simp]
theorem map₂.app.snd
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    (x : CategoricalPullback u ((FiberedCategoryOver.Groupoids.toFibered D).obj X).p) :
    ((map₂ u eta).hom.toNatTrans.app x).snd = eta.hom.toNatTrans.app x.snd := sorry

/-- Components of a pulled-back groupoid-fibred `2`-morphism are natural in the categorical-
pullback object. -/
theorem map₂.naturality
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    {x y : CategoricalPullback u ((FiberedCategoryOver.Groupoids.toFibered D).obj X).p}
    (f : x ⟶ y) :
    (FiberedCategoryOver.Groupoids.toFunctor (map u F)).map f ≫
        (map₂ u eta).hom.toNatTrans.app y =
      (map₂ u eta).hom.toNatTrans.app x ≫
        (FiberedCategoryOver.Groupoids.toFunctor (map u G)).map f := sorry

/-- Pullback in groupoids preserves identity `2`-morphisms. -/
@[simp]
theorem map₂.id
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D} (F : X ⟶ Y) :
    map₂ u (𝟙 F) = 𝟙 (map u F) := sorry

/-- Pullback in groupoids preserves vertical composition of `2`-morphisms. -/
@[simp]
theorem map₂.comp
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ u (eta ≫ theta) = map₂ u eta ≫ map₂ u theta := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

