/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Groupoids.Forgetful
public import ReasLib.CategoryTheory.Fibered.Pullback.Pseudofunctor

/-!
# Construction of fixed-base pullback for categories fibred in groupoids

The neutral fibred-category pullback pseudofunctor is precomposed with the canonical forgetful
pseudofunctor from groupoid-fibred categories and then forgotten to based categories. Its image
still has groupoid fibres, so the generic full-subbicategory lift gives the desired pseudofunctor.
Only the final object-membership witness is new Prop-valued data.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace FiberedCategoryOver.Groupoids.Pullback

/-- The based-category-valued action underlying fixed-base pullback of categories fibred in
groupoids. It is obtained entirely by composing the canonical forgetful and neutral pullback
pseudofunctors. -/
noncomputable def ambient (u : C ⥤ D) :
    Pseudofunctor
      (FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D)
      (BasedCategory.{max vC vS, max uC (max uS vD)} C) :=
  ((FiberedCategoryOver.Groupoids.toFibered D).toPseudofunctor.comp
      (FiberedCategoryOver.Pullback.pseudofunctor u)).comp
    (FiberedCategoryOver.toBased C).toPseudofunctor

/-- Every object in the ambient pullback image remains fibred in groupoids. This is the sole
object-membership input to the full-subbicategory lift. -/
theorem ambient.obj.inGroupoids (u : C ⥤ D)
    (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    BasedCategory.isFiberedInGroupoids C ((ambient u).obj X) := sorry

/-- Pullback along the fixed base functor `u` as a pseudofunctor between bicategories of
categories fibred in groupoids. Its non-Prop object, `1`-cell, `2`-cell, and comparison data are
inherited from the neutral fibred-category pullback pseudofunctor. -/
noncomputable def pseudofunctor (u : C ⥤ D) :
    Pseudofunctor
      (FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D)
      (FiberedCategoryOver.Groupoids.{uC, vC,
        max uC (max uS vD), max vC vS} C) :=
  ObjectProperty.FullSubbicategory.liftPseudofunctor
    (ambient u) (ambient.obj.inGroupoids u)

end FiberedCategoryOver.Groupoids.Pullback

namespace FiberedCategoryOver.Groupoids

/-- Pull a category fibred in groupoids back along an arbitrary functor. This is the object action
of the canonical fixed-base pullback pseudofunctor. -/
noncomputable def pullback
    (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    FiberedCategoryOver.Groupoids.{uC, vC,
      max uC (max uS vD), max vC vS} C :=
  (Pullback.pseudofunctor u).obj X

end FiberedCategoryOver.Groupoids

end CategoryTheory
