/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.Vanishing
public import ReasLib.CategoryTheory.Sites.Grothendieck.Vanishing

/-!
# Lemma 85.8.5

In Situation 85.3.3, for `K` in `D(C_total)`: vanishing of `H^{-p}(C_p, K_p)`
for all `p ≥ 0` implies `H^0(C_total, K) = 0`, and vanishing of
`RΓ(C_p, K_p)` for all `p ≥ 0` implies `RΓ(C_total, K) = 0`.
-/

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

/- Lemma 85.8.5 (1): If stage hypercohomology vanishes in degree `-p` for every nonnegative stage `p`,
then degree-zero hypercohomology of the total simplicial site vanishes. -/
@[stacks 0H0W]
#check (CategoryTheory.SimplicialSites.isZero_H0_of_diagonal_vanishing C J :
    ∀ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (h : ∀ p : ℕ, IsZero ((unboundedPageOneFunctorNonneg C J p (-(p : ℤ))).obj K)),
    IsZero ((unboundedAbutmentFunctor C J 0).obj K))

/- Lemma 85.8.5 (2): If derived global sections vanish at every nonnegative stage, then derived global
sections of the total simplicial site vanish. -/
@[stacks 0H0W]
#check (CategoryTheory.SimplicialSites.isZero_rGamma_of_stage_rGamma C J :
    ∀ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (h : ∀ p : ℕ, IsZero ((RightDerived.Cochain.functor (sectionsStageGamma C J p)).obj K)),
    IsZero ((unboundedRGammaFunctor C J).obj K))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [∀ n : ℕ,
    (toDerived (fiberSectionsStageGamma F J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]
variable [(toDerived (fiberSectionsTotalFunctor F J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]

/- Lemma 85.8.5 (3): If fiber hypercohomology vanishes in degree `-p` for every nonnegative stage `p`,
then degree-zero hypercohomology of the total fiberwise simplicial site vanishes. -/
@[stacks 0H0W]
#check (CategoryTheory.Grothendieck.fiber_isZero_H0_of_diagonal_vanishing F J :
    ∀ (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (h : ∀ p : ℕ, IsZero ((fiberUnboundedPageOneFunctorNonneg F J p (-(p : ℤ))).obj K)),
    IsZero ((fiberUnboundedAbutmentFunctor F J 0).obj K))

/- Lemma 85.8.5 (4): If derived global sections vanish on every nonnegative fiber, then derived global
sections of the total fiberwise simplicial site vanish. -/
@[stacks 0H0W]
#check (CategoryTheory.Grothendieck.fiber_isZero_rGamma_of_stage_rGamma F J :
    ∀ (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (h : ∀ p : ℕ, IsZero ((RightDerived.Cochain.functor (fiberSectionsStageGamma F J p)).obj K)),
    IsZero ((fiberUnboundedRGammaFunctor F J).obj K))

end CategoryTheory.Grothendieck
