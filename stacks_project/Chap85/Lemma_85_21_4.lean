/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.CategoryTheory.Sites.Hypercovering.CartesianDerivedEquivalence

/-!
# Lemma 85.21.4

Let `C` be a site with fibre products and `X` an object of `C`. Let
`a : U ⟶ X` be a hypercovering of `X` in `C`. Let `A` denote the weak Serre
subcategory of cartesian abelian sheaves on `(C / U)_total`. Then `a⁻¹`
defines an equivalence `D⁺(C / X) ≌ D_A⁺((C / U)_total)` with quasi-inverse
`Ra_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open Functor
open SemiRepresentableFamily
  (overSiteDiagram overSiteTotalTopology totalForget directImage
    cartesianProperty overSitePrecoverage)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
variable (hA : A.IsHypercovering J)
variable [HasSheafify (J.over A.right) AddCommGrpCat.{max w u v}]
variable [HasSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over A.right)
          (toHypercovering.{w} A hA).toSimplicialObject n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over A.right)
          (toHypercovering.{w} A hA).toSimplicialObject n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    (Type (max w u v))]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{w} A hA).toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget (toHypercovering.{w} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [(directImage (J.over A.right)
      (Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)).simplicial
      AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology (J.over A.right)
          (Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA)).simplicial)
        AddCommGrpCat.{max w u v}))]

/- Lemma 85.21.4: Let `C` be a site with fibre products and `X` an object of
`C`. Let `a : U ⟶ X` be a hypercovering of `X` in `C` as defined above. Let `A`
denote the weak Serre subcategory of cartesian abelian sheaves on
`(C / U)_total`. Then `a⁻¹` defines an equivalence
`D⁺(C / X) ≌ D_A⁺((C / U)_total)` with quasi-inverse `Ra_*`. -/
@[stacks 0DA9] #check
  (CategoryTheory.Hypercovering.plusCartesianEquivalence J A.right (toHypercovering.{w} A hA) :
    DerivedCategory.Plus (Sheaf (J.over A.right) AddCommGrpCat.{max w u v}) ≌
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
          AddCommGrpCat.{max w u v}))

/- Cartesian abelian sheaves on the total site form a weak Serre subcategory. -/
#check
  (CategoryTheory.Hypercovering.cartesianProperty_isWeakSerreClass J A.right
      (toHypercovering.{w} A hA) :
    IsWeakSerreClass
      (cartesianProperty (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
        AddCommGrpCat.{max w u v}))

/- The forward functor is the canonical corestricted inverse image `a⁻¹`. -/
#check
  (CategoryTheory.Hypercovering.plusCartesianEquivalence_functor J A.right
      (toHypercovering.{w} A hA) :
    (CategoryTheory.Hypercovering.plusCartesianEquivalence J A.right
      (toHypercovering.{w} A hA)).functor =
      CategoryTheory.Hypercovering.plusCartesianFunctor J A.right (toHypercovering.{w} A hA))

/- The inverse functor is the canonical restricted derived direct image `Ra_*`. -/
#check
  (CategoryTheory.Hypercovering.plusCartesianEquivalence_inverse J A.right
      (toHypercovering.{w} A hA) :
    (CategoryTheory.Hypercovering.plusCartesianEquivalence J A.right
      (toHypercovering.{w} A hA)).inverse =
      CategoryTheory.Hypercovering.plusCartesianInverse J A.right (toHypercovering.{w} A hA))

end CategoryTheory.SimplicialObject.Augmented
