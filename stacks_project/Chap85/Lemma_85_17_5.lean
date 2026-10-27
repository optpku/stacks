/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.CartesianDerivedEquivalence
import StacksCheckRecall

/-!
# Lemma 85.17.5

Let `C` be a site with equalizers and fibre products, and let `K` be a
hypercovering. If `A` is the weak Serre subcategory of cartesian abelian sheaves on
`(C / K)_total`, then `a⁻¹` implements an equivalence `D⁺(C) ≌ D_A⁺((C / K)_total)`
with quasi-inverse `Ra_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open Functor
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasSheafify J AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [(directImage J K.simplicial AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))]

/- Lemma 85.17.5: Derived inverse image induces the bounded-below cartesian derived
equivalence, with quasi-inverse the derived direct image. -/
@[stacks 0D8I] #check (CategoryTheory.SemiRepresentableFamily.plusCartesianEquivalence J K :
  DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) ≌
    DerivedCategory.Plus.CohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}))

#check (CategoryTheory.SemiRepresentableFamily.cartesianProperty_isWeakSerreClass J K :
  IsWeakSerreClass (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}))

#check (CategoryTheory.SemiRepresentableFamily.plusCartesianEquivalence_functor J K :
  (plusCartesianEquivalence J K).functor = plusCartesianFunctor J K)

#check (CategoryTheory.SemiRepresentableFamily.plusCartesianEquivalence_inverse J K :
  (plusCartesianEquivalence J K).inverse = plusCartesianInverse J K)

end CategoryTheory.SemiRepresentableFamily
