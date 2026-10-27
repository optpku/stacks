/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.CartesianDerivedEquivalence
import StacksCheckRecall

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

/- Lemma 85.19.4: Derived inverse image along a hypercovering of an object induces
the bounded-below cartesian derived equivalence, with quasi-inverse the derived
direct image. -/
@[stacks 0D8M] #check (CategoryTheory.Hypercovering.plusCartesianEquivalence J X K :
  DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max w u v}) ≌
    DerivedCategory.Plus.CohomologyIn
      (cartesianProperty (J.over X) K.toSimplicialObject
        AddCommGrpCat.{max w u v}))

#check (CategoryTheory.Hypercovering.cartesianProperty_isWeakSerreClass J X K :
  IsWeakSerreClass
    (cartesianProperty (J.over X) K.toSimplicialObject
      AddCommGrpCat.{max w u v}))

#check (CategoryTheory.Hypercovering.plusCartesianEquivalence_functor J X K :
  (plusCartesianEquivalence J X K).functor = plusCartesianFunctor J X K)

#check (CategoryTheory.Hypercovering.plusCartesianEquivalence_inverse J X K :
  (plusCartesianEquivalence J X K).inverse = plusCartesianInverse J X K)

end CategoryTheory.Hypercovering
