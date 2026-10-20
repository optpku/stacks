/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.Representable.Presentation

@[expose] public section
open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.FiberedCategoryOver.Groupoids
open scoped Bicategory
universe u v
namespace CategoryTheory.FiberedCategoryOver.Groupoids.Presentation
variable {C : Type u} [Category.{v} C]
variable {𝒳 𝒴 : FiberedCategoryOver.Groupoids C} {X Y : C}

/-- A morphism of slice fibrations is `2`-isomorphic to the canonical `overMap` of its
terminal-object evaluation. Objectwise the comparison is the identity on the underlying
object of the base category. -/
def sliceIso (G : slice X ⟶ slice Y) :
    G ≅ overMap (slice.eval G) := by
  refine InducedBicategory.isoMk
    (BasedNatIso.ofComponents
      (fun a ↦ Over.isoMk ((commIso G).app a) ?_) ?_ ?_)
  all_goals sorry

/-- The unit/counit triangle relating `f ≫ eY.hom` to the presentation of `f` through
`eX`. -/
def unitIso (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y) (f : 𝒳 ⟶ 𝒴) :
    (f ≫ eY.hom) ≅ eX.hom ≫ ((eX.inv ≫ f) ≫ eY.hom) :=
  (λ_ (f ≫ eY.hom)).symm ≪≫
    whiskerRightIso eX.unit (f ≫ eY.hom) ≪≫
    α_ eX.hom eX.inv (f ≫ eY.hom) ≪≫
    whiskerLeftIso eX.hom (α_ eX.inv f eY.hom).symm

/-- The recover triangle: `f ≫ eY.hom` is `2`-isomorphic to
`eX.hom ≫ overMap (recover eX eY f)`. -/
def triangle (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y) (f : 𝒳 ⟶ 𝒴) :
    (f ≫ eY.hom) ≅ eX.hom ≫ overMap (recover eX eY f) :=
  unitIso eX eY f ≪≫ whiskerLeftIso eX.hom (sliceIso _)

/-- The total-functor form of `triangle`. -/
def triangleToFunctor (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y)
    (f : 𝒳 ⟶ 𝒴) :
    toFunctor (f ≫ eY.hom) ≅
      toFunctor (eX.hom ≫ overMap (recover eX eY f)) :=
  toFunctorIso (triangle eX eY f)


end CategoryTheory.FiberedCategoryOver.Groupoids.Presentation
