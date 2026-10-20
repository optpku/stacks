/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.StandardResolution

/-!
# Standard polynomial resolution as a polynomial-site object

The shared standard resolution supplies the augmentation of `CommAlgCat A` and
the cosimplicial object of `PolynomialSite A B`.
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

#check (Algebra.PolynomialSite.standardAugmented A B :
  SimplicialObject.Augmented (CommAlgCat.{u} A))

#check (Algebra.PolynomialSite.standardAugmented_left A B :
    (standardAugmented A B).left =
      ((evaluation (CommRingCat.of A)).obj ((CommRingCat.of A).mkUnder B)).left ⋙
        (commAlgCatEquivUnder (CommRingCat.of A)).inverse)

#check (Algebra.PolynomialSite.standardHom A B :
    (standardAugmented A B).left ⟶
      (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))

#check (Algebra.PolynomialSite.standardHom_app A B :
  ∀ n : SimplexCategoryᵒᵖ,
    (standardHom A B).app n =
      (standardAugmented A B).hom.app n ≫
        (commAlgCatEquivUnder (CommRingCat.of A)).unitIso.inv.app (CommAlgCat.of A B))

#check (Algebra.PolynomialSite.standard_isPolynomial A B :
  ∀ n : SimplexCategoryᵒᵖ, IsPolynomial A ((standardAugmented A B).left.obj n))

#check (Algebra.PolynomialSite.standardHom_rlp A B :
  I.rlp (underlyingSSetMap (standardHom A B)))

#check (Algebra.PolynomialSite.standardCosimplicial A B :
  CosimplicialObject (PolynomialSite A B))

#check (Algebra.PolynomialSite.standardCosimplicial_obj A B :
  ∀ n : SimplexCategory,
    ((standardCosimplicial A B).obj n).unop.obj =
      Over.mk ((standardHom A B).app (Opposite.op n)))

end Algebra.PolynomialSite
