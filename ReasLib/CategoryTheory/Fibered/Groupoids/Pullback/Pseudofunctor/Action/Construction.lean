module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor.Construction

/-!
# Direct action of fixed-base pullback in groupoids

This file owns the application-facing `1`-cell, `2`-cell, and hom-functor actions of pullback for
categories fibred in groupoids.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

open CategoryTheory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- Pullback of a `1`-morphism between categories fibred in groupoids. -/
noncomputable def map
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D} (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.pullback u X ⟶
      FiberedCategoryOver.Groupoids.pullback u Y :=
  (pseudofunctor u).map F

/-- Pullback of a `2`-morphism between morphisms of categories fibred in groupoids. -/
noncomputable def map₂
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) : map u F ⟶ map u G :=
  (pseudofunctor u).map₂ eta

/-- For fixed `u`, pullback acts functorially on each hom category of categories fibred in
groupoids. -/
noncomputable def mapFunctor
    (X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    (X ⟶ Y) ⥤
      (FiberedCategoryOver.Groupoids.pullback u X ⟶
        FiberedCategoryOver.Groupoids.pullback u Y) :=
  (pseudofunctor u).mapFunctor X Y

end CategoryTheory.FiberedCategoryOver.Groupoids.Pullback
