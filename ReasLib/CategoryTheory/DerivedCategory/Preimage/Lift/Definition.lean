module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifts to selected cochain representatives

This file records a morphism of selected cochain representatives together with the statement that
its image in the derived category is a prescribed morphism.  The construction depends only on the
canonical object preimages of the localization functor and is independent of any filtration or
spectral sequence.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Preimage

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- A cochain-map lift of a derived morphism between the selected object preimages.

The localization equation is retained as part of the datum, since the objectwise choice
`DerivedCategory.Q.objPreimage` is not functorial. -/
@[stacks 0BKM "cochain lift between selected derived-category preimages"]
structure Lift {K L : DerivedCategory A} (f : K ⟶ L) where
  /-- The cochain map between the selected representatives. -/
  hom : DerivedCategory.Q.objPreimage K ⟶ DerivedCategory.Q.objPreimage L
  /-- The image of `hom` under the localization functor represents `f`. -/
  comm :
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A).map hom =
      (DerivedCategory.Q.objObjPreimageIso K).hom ≫ f ≫
        (DerivedCategory.Q.objObjPreimageIso L).inv

namespace Lift

/-- The localization specification carried by a lift between selected cochain representatives. -/
@[stacks 0BKM "localization specification of a selected-preimage lift"]
theorem map_eq {K L : DerivedCategory A} {f : K ⟶ L} (l : Lift f) :
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A).map l.hom =
      (DerivedCategory.Q.objObjPreimageIso K).hom ≫ f ≫
        (DerivedCategory.Q.objObjPreimageIso L).inv := sorry

end Lift

end CategoryTheory.DerivedCategory.Preimage
