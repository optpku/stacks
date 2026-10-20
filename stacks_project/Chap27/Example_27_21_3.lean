/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.DegreeOneCounterexample
import StacksCheckRecall

@[expose] public section

universe u v w z

#check (MvPolynomial.standardGrading :
  ∀ (σ : Type u) (R : Type v) [CommRing R],
    ℕ → Submodule R (MvPolynomial σ R))

#check (GradedAlgebra.Quotient.grading :
  ∀ {ι : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A],
    (ι → Submodule R A) → (J : Ideal A) → [J.IsTwoSided] → ι →
      Submodule R (A ⧸ J))

#check (GradedAlgebra.Quotient.spanSingletonGradedAlgebra :
  ∀ {ι : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : ι → Submodule R A) [DecidableEq ι] [AddMonoid ι]
    [GradedAlgebra 𝒜] {a : A}
    [(Ideal.span ({a} : Set A)).IsTwoSided],
    SetLike.IsHomogeneousElem 𝒜 a →
      GradedAlgebra (GradedAlgebra.Quotient.grading 𝒜 (Ideal.span ({a} : Set A))))

#check (HomogeneousLocalization.Away.Module.degreeZeroPart :
  ∀ {ι : Type u} {S : Type v} {σ : Type w} {M : Type z} {τ : Type z}
    [AddCommMonoid ι] [DecidableEq ι] [CommRing S]
    [SetLike σ S] [AddSubgroupClass σ S]
    [AddCommMonoid M] [Module S M] [SetLike τ M] [AddSubmonoidClass τ M]
    (𝒜 : ι → σ) (ℳ : ι → τ) [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]
    {d : ι} (f : 𝒜 d),
    Submodule (HomogeneousLocalization.Away 𝒜 (f : S))
      (LocalizedModule.Away (f : S) M))

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

#check (AlgebraicGeometry.Proj.basicOpen :
  ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜], A → (AlgebraicGeometry.Proj 𝒜).Opens)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : AlgebraicGeometry.Proj.basicOpen 𝒜 g ≤
          AlgebraicGeometry.Proj.basicOpen 𝒜 f),
      AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMapType
        𝒜 ℳ hf hm hg hn hgf)

end


#check (IsSymmetricAlgebra :
  ∀ {R : Type u} {M : Type v} {A : Type w}
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A],
    (M →ₗ[R] A) → Prop)

namespace AlgebraicGeometry.Proj.DegreeOneCounterexample

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.Coordinate : Type)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.baseIdeal :
  ∀ (k : Type u) [Field k], Ideal (MvPolynomial Coordinate k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.BaseRing :
  ∀ (k : Type u) [Field k], Type u)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.FreeModule :
  ∀ (k : Type u) [Field k], Type u)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.relationVector :
  ∀ (k : Type u) [Field k], FreeModule k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.relationSubmodule :
  ∀ (k : Type u) [Field k], Submodule (BaseRing k) (FreeModule k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.PresentedModule :
  ∀ (k : Type u) [Field k], Type u)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.witness :
  ∀ (k : Type u) [Field k], PresentedModule k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.PolynomialRing :
  ∀ (k : Type u) [Field k], Type u)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.symmetricRelation :
  ∀ (k : Type u) [Field k], PolynomialRing k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.symmetricIdeal :
  ∀ (k : Type u) [Field k], Ideal (PolynomialRing k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.SymmetricPresentation :
  ∀ (k : Type u) [Field k], Type u)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.symmetricQuotientMap :
  ∀ (k : Type u) [Field k], PolynomialRing k →ₐ[BaseRing k] SymmetricPresentation k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.symmetricRelation_isHomogeneous :
  ∀ (k : Type u) [Field k],
    SetLike.IsHomogeneousElem
      (MvPolynomial.standardGrading (Fin 2) (BaseRing k)) (symmetricRelation k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.grading :
  ∀ (k : Type u) [Field k], ℕ → Submodule (BaseRing k) (SymmetricPresentation k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.instGradedAlgebra :
  ∀ (k : Type u) [Field k], GradedAlgebra (grading k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.witnessPolynomial :
  ∀ (k : Type u) [Field k], PolynomialRing k)

#check
  (AlgebraicGeometry.Proj.DegreeOneCounterexample.witnessPolynomial_mem_homogeneousSubmodule :
    ∀ (k : Type u) [Field k],
      witnessPolynomial k ∈ MvPolynomial.standardGrading (Fin 2) (BaseRing k) 1)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.witnessDegreeOneClass_mem :
  ∀ (k : Type u) [Field k],
    symmetricQuotientMap k (witnessPolynomial k) ∈ grading k 1)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.witnessDegreeOneClass :
  ∀ (k : Type u) [Field k], grading k 1)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.linearPolynomial :
  ∀ (k : Type u) [Field k], FreeModule k → PolynomialRing k)

#check
  (AlgebraicGeometry.Proj.DegreeOneCounterexample.linearPolynomial_mem_homogeneousSubmodule :
    ∀ (k : Type u) [Field k] (z : FreeModule k),
      linearPolynomial k z ∈ MvPolynomial.standardGrading (Fin 2) (BaseRing k) 1)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.linearPolynomialClass_mem_grading :
  ∀ (k : Type u) [Field k] (z : FreeModule k),
    symmetricQuotientMap k (linearPolynomial k z) ∈ grading k 1)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.freeToDegreeOne :
  ∀ (k : Type u) [Field k], FreeModule k →ₗ[BaseRing k] grading k 1)

#check
  (AlgebraicGeometry.Proj.DegreeOneCounterexample.relationSubmodule_le_ker_freeToDegreeOne :
    ∀ (k : Type u) [Field k],
      relationSubmodule k ≤ LinearMap.ker (freeToDegreeOne k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.moduleToDegreeOne :
  ∀ (k : Type u) [Field k], PresentedModule k →ₗ[BaseRing k] grading k 1)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.moduleToPresentation :
  ∀ (k : Type u) [Field k],
    PresentedModule k →ₗ[BaseRing k] SymmetricPresentation k)

#check
  (AlgebraicGeometry.Proj.DegreeOneCounterexample.moduleToPresentation_isSymmetricAlgebra :
    ∀ (k : Type u) [Field k], IsSymmetricAlgebra (moduleToPresentation k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.moduleToDegreeOne_witness :
  ∀ (k : Type u) [Field k],
    moduleToDegreeOne k (witness k) = witnessDegreeOneClass k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.shiftOneGrading :
  ∀ (k : Type u) [Field k], ℕ → Submodule (BaseRing k) (SymmetricPresentation k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.instGradedSMulShiftOne :
  ∀ (k : Type u) [Field k], SetLike.GradedSMul (grading k) (shiftOneGrading k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.xClass :
  ∀ (k : Type u) [Field k], SymmetricPresentation k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.yClass :
  ∀ (k : Type u) [Field k], SymmetricPresentation k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.xyClass :
  ∀ (k : Type u) [Field k], SymmetricPresentation k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.xClass_mem_grading :
  ∀ (k : Type u) [Field k], xClass k ∈ grading k 1)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.yClass_mem_grading :
  ∀ (k : Type u) [Field k], yClass k ∈ grading k 1)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.xyClass_mem_grading :
  ∀ (k : Type u) [Field k], xyClass k ∈ grading k 2)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.XChartDegreeOneSections :
  ∀ (k : Type u) [Field k],
    Submodule (HomogeneousLocalization.Away (grading k) (xClass k))
      (LocalizedModule.Away (xClass k) (SymmetricPresentation k)))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.YChartDegreeOneSections :
  ∀ (k : Type u) [Field k],
    Submodule (HomogeneousLocalization.Away (grading k) (yClass k))
      (LocalizedModule.Away (yClass k) (SymmetricPresentation k)))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.XYChartDegreeOneSections :
  ∀ (k : Type u) [Field k],
    Submodule (HomogeneousLocalization.Away (grading k) (xyClass k))
      (LocalizedModule.Away (xyClass k) (SymmetricPresentation k)))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.basicOpen_xy_le_x :
  ∀ (k : Type u) [Field k],
    Proj.basicOpen (grading k) (xyClass k) ≤ Proj.basicOpen (grading k) (xClass k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.basicOpen_xy_le_y :
  ∀ (k : Type u) [Field k],
    Proj.basicOpen (grading k) (xyClass k) ≤ Proj.basicOpen (grading k) (yClass k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.restrictXToXY :
  ∀ (k : Type u) [Field k], XChartDegreeOneSections k →+ XYChartDegreeOneSections k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.restrictYToXY :
  ∀ (k : Type u) [Field k], YChartDegreeOneSections k →+ XYChartDegreeOneSections k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.degreeOneToXChart :
  ∀ (k : Type u) [Field k], grading k 1 →+ XChartDegreeOneSections k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.degreeOneToYChart :
  ∀ (k : Type u) [Field k], grading k 1 →+ YChartDegreeOneSections k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.restrictXToXY_degreeOneToXChart :
  ∀ (k : Type u) [Field k] (z : grading k 1),
    restrictXToXY k (degreeOneToXChart k z) =
      ⟨HomogeneousLocalization.Away.Module.powMk (grading k)
          ⟨xyClass k, xyClass_mem_grading k⟩ 0 z,
        HomogeneousLocalization.Away.Module.mk_mem_degreeZeroPart
          (grading k) (shiftOneGrading k) ⟨xyClass k, xyClass_mem_grading k⟩
          (n := 0) (by simpa [shiftOneGrading] using z.2)⟩)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.restrictYToXY_degreeOneToYChart :
  ∀ (k : Type u) [Field k] (z : grading k 1),
    restrictYToXY k (degreeOneToYChart k z) =
      ⟨HomogeneousLocalization.Away.Module.powMk (grading k)
          ⟨xyClass k, xyClass_mem_grading k⟩ 0 z,
        HomogeneousLocalization.Away.Module.mk_mem_degreeZeroPart
          (grading k) (shiftOneGrading k) ⟨xyClass k, xyClass_mem_grading k⟩
          (n := 0) (by simpa [shiftOneGrading] using z.2)⟩)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.degreeOneCechDifferential :
  ∀ (k : Type u) [Field k],
    XChartDegreeOneSections k × YChartDegreeOneSections k →+ XYChartDegreeOneSections k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.DegreeOneGlobalSections :
  ∀ (k : Type u) [Field k],
    AddSubgroup (XChartDegreeOneSections k × YChartDegreeOneSections k))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.degreeOneGlobalSections_spec :
  ∀ (k : Type u) [Field k]
    (z : XChartDegreeOneSections k × YChartDegreeOneSections k),
    z ∈ (degreeOneCechDifferential k).ker ↔
      restrictXToXY k z.1 = restrictYToXY k z.2)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.degreeOneSection_compatible :
  ∀ (k : Type u) [Field k] (z : grading k 1),
    degreeOneCechDifferential k (degreeOneToXChart k z, degreeOneToYChart k z) = 0)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.degreeOneSection :
  ∀ (k : Type u) [Field k], grading k 1 →+ DegreeOneGlobalSections k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.degreeOneSection_apply :
  ∀ (k : Type u) [Field k] (z : grading k 1),
    (degreeOneSection k z : XChartDegreeOneSections k × YChartDegreeOneSections k) =
      (degreeOneToXChart k z, degreeOneToYChart k z))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.basicOpen_x_sup_y :
  ∀ (k : Type u) [Field k],
    Proj.basicOpen (grading k) (xClass k) ⊔ Proj.basicOpen (grading k) (yClass k) = ⊤)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.sectionMap :
  ∀ (k : Type u) [Field k], PresentedModule k →+ DegreeOneGlobalSections k)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.sectionMap_apply :
  ∀ (k : Type u) [Field k] (m : PresentedModule k),
    sectionMap k m = degreeOneSection k (moduleToDegreeOne k m))

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.witnessDegreeOneClass_mapsToZeroOnX :
  ∀ (k : Type u) [Field k], degreeOneToXChart k (witnessDegreeOneClass k) = 0)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.witnessDegreeOneClass_mapsToZeroOnY :
  ∀ (k : Type u) [Field k], degreeOneToYChart k (witnessDegreeOneClass k) = 0)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.witness_mapsToZero :
  ∀ (k : Type u) [Field k], sectionMap k (witness k) = 0)

#check (AlgebraicGeometry.Proj.DegreeOneCounterexample.witness_ne_zero :
  ∀ (k : Type u) [Field k], witness k ≠ 0)

end AlgebraicGeometry.Proj.DegreeOneCounterexample

/- Example 27.21.3: the canonical degree-one map from an explicitly presented module to the
two-chart global-section model of its degree-one twist need not be injective. -/
@[stacks 01OC] #check
  (AlgebraicGeometry.Proj.DegreeOneCounterexample.sectionMap_not_injective :
    ∀ (k : Type u) [Field k],
      ¬ Function.Injective (AlgebraicGeometry.Proj.DegreeOneCounterexample.sectionMap k))
