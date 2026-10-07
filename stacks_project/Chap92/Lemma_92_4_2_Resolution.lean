module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import stacks_project.Chap92.Lemma_92_4_1_Evaluation

/-!
# Standard polynomial resolution as a polynomial-site object

This leaf converts the standard simplicial resolution of `B` over `A` into an
augmentation of `CommAlgCat A` and a cosimplicial object of `PolynomialSite A B`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.CommRingCat.Under.PolynomialResolution
open Algebra
open SSet.modelCategoryQuillen
open Under

universe u

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The standard simplicial polynomial resolution of `B` over `A`, as an augmented
simplicial object of `CommAlgCat A`. -/
noncomputable def standardAugmented : SimplicialObject.Augmented (CommAlgCat.{u} A) :=
  (SimplicialObject.Augmented.whiskeringObj (Under (CommRingCat.of A))
      (CommAlgCat.{u} A) (commAlgCatEquivUnder (CommRingCat.of A)).inverse).obj
    ((evaluation (CommRingCat.of A)).obj ((CommRingCat.of A).mkUnder B))

/-- The simplicial object of the standard polynomial resolution of `B` over `A`. -/
theorem standardAugmented_left :
    (standardAugmented A B).left =
      ((evaluation (CommRingCat.of A)).obj ((CommRingCat.of A).mkUnder B)).left ⋙
        (commAlgCatEquivUnder (CommRingCat.of A)).inverse :=
  sorry

/-- The standard-resolution augmentation `ε : P_• ⟶ B` as a morphism of simplicial
`A`-algebras. -/
noncomputable def standardHom :
    (standardAugmented A B).left ⟶
      (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B) :=
  (standardAugmented A B).hom ≫
    (const (CommAlgCat.{u} A)).map
      ((commAlgCatEquivUnder (CommRingCat.of A)).unitIso.inv.app (CommAlgCat.of A B))

/-- Components of `standardHom` are the transported standard-resolution augmentation
maps. -/
theorem standardHom_app (n : SimplexCategoryᵒᵖ) :
    (standardHom A B).app n =
      (standardAugmented A B).hom.app n ≫
        (commAlgCatEquivUnder (CommRingCat.of A)).unitIso.inv.app (CommAlgCat.of A B) :=
  sorry

/-- Each term of the standard polynomial resolution of `B` over `A` is a polynomial
`A`-algebra. -/
instance standard_isPolynomial (n : SimplexCategoryᵒᵖ) :
    IsPolynomial A ((standardAugmented A B).left.obj n) :=
  sorry

/-- The underlying simplicial-set map of the standard resolution is a trivial Kan
fibration. -/
theorem standardHom_rlp : I.rlp (underlyingSSetMap (standardHom A B)) :=
  sorry

/-- The standard polynomial resolution of `B` over `A`, as a cosimplicial object of
`PolynomialSite A B`. -/
noncomputable def standardCosimplicial : CosimplicialObject (PolynomialSite A B) :=
  asCosimplicial (standardHom A B) (standard_isPolynomial A B)

/-- Unpacking `standardCosimplicial` in each degree recovers the corresponding
standard augmentation component. -/
theorem standardCosimplicial_obj (n : SimplexCategory) :
    ((standardCosimplicial A B).obj n).unop.obj =
      Over.mk ((standardHom A B).app (Opposite.op n)) :=
  sorry

end Algebra.PolynomialSite
