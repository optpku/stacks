/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import stacks_project.Chap85.Lemma_85_19_4

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

/-- Cartesian abelian sheaves on `(C / U)_total` form a weak Serre subcategory of
`Ab((C / U)_total)`. -/
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass
      (cartesianProperty (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
        AddCommGrpCat.{max w u v}) :=
  Hypercovering.cartesianProperty_isWeakSerreClass J A.right (toHypercovering.{w} A hA)

/-- The functor `a⁻¹` corestricted from `D⁺(C / X)` to `D_A⁺((C / U)_total)`, where
`A` is the object property of cartesian abelian sheaves. -/
abbrev plusCartesianFunctor :
    DerivedCategory.Plus (Sheaf (J.over A.right) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
          AddCommGrpCat.{max w u v}) :=
  Hypercovering.plusCartesianFunctor J A.right (toHypercovering.{w} A hA)

/-- The functor sending an object of `D_A⁺((C / U)_total)` to `Ra_*` of its
underlying object of `D⁺((C / U)_total)`. -/
abbrev plusCartesianInverse :
    DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
          AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus (Sheaf (J.over A.right) AddCommGrpCat.{max w u v}) :=
  Hypercovering.plusCartesianInverse J A.right (toHypercovering.{w} A hA)

/-- Lemma 85.21.4: Let `C` be a site with fibre products and `X` an object of
`C`. Let `a : U ⟶ X` be a hypercovering of `X` in `C` as defined above. Let `A`
denote the weak Serre subcategory of cartesian abelian sheaves on
`(C / U)_total`. Then `a⁻¹` defines an equivalence
`D⁺(C / X) ≌ D_A⁺((C / U)_total)` with quasi-inverse `Ra_*`. -/
@[stacks 0DA9]
def plusCartesianEquivalence :
    DerivedCategory.Plus (Sheaf (J.over A.right) AddCommGrpCat.{max w u v}) ≌
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
          AddCommGrpCat.{max w u v}) :=
  Hypercovering.plusCartesianEquivalence J A.right (toHypercovering.{w} A hA)

/-- The forward functor of `plusCartesianEquivalence` is `a⁻¹` corestricted to
`D_A⁺((C / U)_total)`. -/
theorem plusCartesianEquivalence_functor :
    (plusCartesianEquivalence J A hA).functor = plusCartesianFunctor J A hA :=
  sorry

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` on
`D_A⁺((C / U)_total)`. -/
theorem plusCartesianEquivalence_inverse :
    (plusCartesianEquivalence J A hA).inverse = plusCartesianInverse J A hA :=
  sorry

/-- The corestricted functor `a⁻¹ : D⁺(C / X) ⥤ D_A⁺((C / U)_total)` is an
equivalence. -/
instance plusCartesianFunctor_isEquivalence :
    (plusCartesianFunctor J A hA).IsEquivalence :=
  Equivalence.isEquivalence_functor (plusCartesianEquivalence J A hA)

end CategoryTheory.SimplicialObject.Augmented
