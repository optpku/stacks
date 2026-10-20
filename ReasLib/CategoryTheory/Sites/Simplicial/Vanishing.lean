/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.UnboundedCohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Functor
open HomologicalComplex ComplexShape DerivedCategory
open RightDerived.Cochain

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]
variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [(globalSectionsTotalFunctor C J).Additive]
variable [∀ n : ℕ,
    (toDerived (sectionsStageGamma C J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]
variable [(toDerived (globalSectionsTotalFunctor C J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]

/-- If stage hypercohomology vanishes in degree `-p` for every nonnegative stage `p`,
then degree-zero hypercohomology of the total simplicial site vanishes. -/
theorem isZero_H0_of_diagonal_vanishing
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (h : ∀ p : ℕ, IsZero ((unboundedPageOneFunctorNonneg C J p (-(p : ℤ))).obj K)) :
    IsZero ((unboundedAbutmentFunctor C J 0).obj K) :=
  sorry

/-- If derived global sections vanish at every nonnegative stage, then derived global
sections of the total simplicial site vanish. -/
theorem isZero_rGamma_of_stage_rGamma
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (h : ∀ p : ℕ, IsZero ((RightDerived.Cochain.functor (sectionsStageGamma C J p)).obj K)) :
    IsZero ((unboundedRGammaFunctor C J).obj K) :=
  sorry

end CategoryTheory.SimplicialSites
