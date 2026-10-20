/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_17_5
public import stacks_project.Chap85.Lemma_85_19_4_Adjunction

/-!
# Lemma 85.19.4

Let `C` be a site with fibre products and `X` an object of `C`. Let `K` be a
hypercovering of `X`. If `A` is the weak Serre subcategory of cartesian abelian
sheaves on `(C / K)_total`, then `a⁻¹` implements an equivalence
`D⁺(C / X) ≌ D_A⁺((C / K)_total)` with quasi-inverse `Ra_*`.
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

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)
variable [HasSheafify (J.over X) AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [(directImage (J.over X) (toSliceTerminal J X K).simplicial
      AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology (J.over X) (toSliceTerminal J X K).simplicial)
        AddCommGrpCat.{max w u v}))]

/-- Cartesian abelian sheaves on `(C / K)_total` form a weak Serre subcategory of
`Ab((C / K)_total)`. -/
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass
      (cartesianProperty (J.over X) K.toSimplicialObject
        AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.cartesianProperty_isWeakSerreClass.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- The functor `a⁻¹` corestricted from `D⁺(C / X)` to `D_A⁺((C / K)_total)`, where
`A` is the object property of cartesian abelian sheaves. -/
abbrev plusCartesianFunctor :
    DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (J.over X) K.toSimplicialObject
          AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.plusCartesianFunctor.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- The functor sending an object of `D_A⁺((C / K)_total)` to `Ra_*` of its
underlying object of `D⁺((C / K)_total)`. -/
abbrev plusCartesianInverse :
    DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (J.over X) K.toSimplicialObject
          AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.plusCartesianInverse.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- Lemma 85.19.4: Let `C` be a site with fibre products and `X` an object of
`C`. Let `K` be a hypercovering of `X`. Let `A` denote the weak Serre subcategory
of cartesian abelian sheaves on `(C / K)_total`. Then `a⁻¹` defines an
equivalence `D⁺(C / X) ≌ D_A⁺((C / K)_total)` with quasi-inverse `Ra_*`. -/
@[stacks 0D8M]
def plusCartesianEquivalence :
    DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max w u v}) ≌
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty (J.over X) K.toSimplicialObject
          AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.plusCartesianEquivalence.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- The forward functor of `plusCartesianEquivalence` is `a⁻¹` corestricted to
`D_A⁺((C / K)_total)`. -/
theorem plusCartesianEquivalence_functor :
    (plusCartesianEquivalence J X K).functor = plusCartesianFunctor J X K :=
  sorry

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` on
`D_A⁺((C / K)_total)`. -/
theorem plusCartesianEquivalence_inverse :
    (plusCartesianEquivalence J X K).inverse = plusCartesianInverse J X K :=
  sorry

/-- The corestricted functor `a⁻¹ : D⁺(C / X) ⥤ D_A⁺((C / K)_total)` is an
equivalence. -/
instance plusCartesianFunctor_isEquivalence :
    (plusCartesianFunctor J X K).IsEquivalence :=
  Equivalence.isEquivalence_functor (plusCartesianEquivalence J X K)

end CategoryTheory.Hypercovering
