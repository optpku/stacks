/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialSiteVanishing
public import ReasLib.RingTheory.CotangentComplex.Comparison
public import ReasLib.RingTheory.CotangentComplex.NaiveComparison
public import ReasLib.RingTheory.CotangentComplex.PolynomialSite
import StacksCheckRecall

/-!
# Kernel vanishing and naive cotangent comparisons on `C_{B/A}`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Algebra Algebra.PolynomialSite
open Algebra.CotangentComplex Algebra.NaiveCotangent
open CommAlgCat.Over.Polynomial CommAlgCat.Over.Polynomial.Site
open CommRingCat.Under.CotangentComplex Site
open CommRingCat.Under.FreeAlgebra
open DerivedCategory.TStructure
open scoped CategoryTheory

noncomputable section

universe u q q'

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

section AbelianGroups

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/- Remark 92.11.1 (1). The derived lower shriek of the kernel presheaf vanishes. -/
@[stacks 08R7] #check (Algebra.PolynomialSite.lowerShriek_kernel_isZero A B :
    IsZero
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (kernelPresheaf A B))))

end AbelianGroups

section Modules

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/- Remark 92.11.1 (2). Degree-zero homology of the conormal presheaf vanishes. -/
@[stacks 08R7] #check (Algebra.PolynomialSite.conormal_homology_zero_isZero A B :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        (((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          (conormalSheaf A B))))

/- Remark 92.11.1 (3). Degree-one homology of the conormal presheaf vanishes. -/
@[stacks 08R7] #check (Algebra.PolynomialSite.conormal_homology_negOne_isZero A B :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1 : ℤ)).obj
        (((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          (conormalSheaf A B))))

end Modules
end Algebra.PolynomialSite

/- Remark 92.11.1. The standard-resolution comparison is a quasi-isomorphism. -/
@[stacks 08R7] #check (CategoryTheory.CommRingCat.Under.CotangentComplex.Comparison.omegaInr_quasiIso :
  ∀ (A : CommRingCat.{u}) (B : Under A),
    QuasiIso (CategoryTheory.CommRingCat.Under.CotangentComplex.Comparison.omegaInr A B))

/- Remark 92.11.1.1. The comparison map to the cotangent complex. -/
@[stacks 08R7] #check (CategoryTheory.CommRingCat.Under.CotangentComplex.Comparison.comparisonDerived :
    ∀ (A : CommRingCat.{u}) (B : Under A) (E : Type u)
      (φ : (functor A).obj E ⟶ B),
      DerivedCategory.Q.obj
        (CategoryTheory.CommRingCat.Under.CotangentComplex.Comparison.kernelDifferentialsComplex
          A B E φ) ⟶
        DerivedCategory.Q.obj
          (CategoryTheory.CommRingCat.Under.CotangentComplex.Comparison.objRestrictScalars A B))

/- Remark 92.11.1.2. The truncated comparison map. -/
@[stacks 08R7] #check (Algebra.NaiveCotangent.naiveCotangentToTruncGE :
  ∀ (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B),
    DerivedCategory.Q.obj (naiveComplex A B E φ) ⟶
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)))

/- Remark 92.11.1. The truncated evaluation isomorphism. -/
@[stacks 08R7] #check (Algebra.NaiveCotangent.truncGEEvaluationIso :
  ∀ (A : CommRingCat.{u}) (B : Under A),
    (t.truncGE (-1)).obj (DerivedCategory.Q.obj (evaluationCone A B)) ≅
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)))

/- Remark 92.11.1. The cotangent complex is computed by the differential presheaf. -/
@[stacks 08R7] #check (Algebra.CotangentComplex.lowerShriek_omega :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
    [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
    [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
      (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
        (ComplexShape.up ℤ))],
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
        ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
            (0 : ℤ)).obj (omegaSheaf A B))))
