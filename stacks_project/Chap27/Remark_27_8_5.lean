/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.PowerQuotient
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u v

section

variable (k : Type u) [Field k]

/- Remark 27.8.5: for `S = k[x, y, z]` and
`M = S / (x^100, y^100, z^100)`, the canonical map from `M₀` to the global sections of its
associated sheaf is not bijective. -/
@[stacks 01M9] #check
  (AlgebraicGeometry.Proj.PowerQuotient.degreeZeroSectionMap_not_bijective
      (σ := Fin 3) (k := k) (100 : ℕ+) :
    ¬ Function.Bijective
      (AlgebraicGeometry.Proj.PowerQuotient.degreeZeroSectionMap
        (σ := Fin 3) (k := k) (100 : ℕ+)))

/- The associated sheaf of the displayed quotient is zero. -/
#check
  (AlgebraicGeometry.Proj.PowerQuotient.associatedSheaf_isZero
      (σ := Fin 3) (k := k) (100 : ℕ+) :
    CategoryTheory.Limits.IsZero
      (AlgebraicGeometry.Proj.PowerQuotient.associatedSheaf
        (σ := Fin 3) (k := k) (100 : ℕ+)))

/- The degree-zero piece of the displayed quotient is canonically the coefficient field. -/
#check
  (MvPolynomial.PowerQuotient.integerDegreeZeroLinearEquiv
      (σ := Fin 3) (k := k) (100 : ℕ+) :
    MvPolynomial.PowerQuotient.integerGrading
      (σ := Fin 3) (k := k) (100 : ℕ+) 0 ≃ₗ[k] k)

end

section AlgebraicClosure

variable {σ : Type u} {k : Type v} [CommRing k]
variable (e : ℕ+)

/- The relation ideal in the adopted algebraic construction. -/
#check
  (MvPolynomial.PowerQuotient.relationIdeal (σ := σ) (k := k) e :
    Ideal (MvPolynomial σ k))

/- The concrete coordinate-power quotient. -/
#check
  (MvPolynomial.PowerQuotient.Quotient (σ := σ) (k := k) e :
    Type (max u v))

/- The canonical quotient map. -/
#check
  (MvPolynomial.PowerQuotient.quotientMap (σ := σ) (k := k) e :
    MvPolynomial σ k →ₐ[k]
      MvPolynomial.PowerQuotient.Quotient (σ := σ) (k := k) e)

/- Homogeneity of the relation ideal. -/
#check
  (MvPolynomial.PowerQuotient.relationIdeal_isHomogeneous
      (σ := σ) (k := k) e :
    (MvPolynomial.PowerQuotient.relationIdeal (σ := σ) (k := k) e).IsHomogeneous
      (MvPolynomial.standardGrading σ k))

/- The quotient grading. -/
#check
  (MvPolynomial.PowerQuotient.grading (σ := σ) (k := k) e :
    ℕ → Submodule k
      (MvPolynomial.PowerQuotient.Quotient (σ := σ) (k := k) e))

/- The graded-algebra structure on the quotient. -/
#check
  (MvPolynomial.PowerQuotient.gradedAlgebra (σ := σ) (k := k) e :
    GradedAlgebra (MvPolynomial.PowerQuotient.grading (σ := σ) (k := k) e))

/- Evaluation at the origin. -/
#check
  (MvPolynomial.PowerQuotient.zeroEval (σ := σ) (k := k) :
    MvPolynomial σ k →ₐ[k] k)

/- Descent of evaluation at the origin through the quotient. -/
#check
  (MvPolynomial.PowerQuotient.relationIdeal_le_ker_zeroEval
      (σ := σ) (k := k) e :
    MvPolynomial.PowerQuotient.relationIdeal (σ := σ) (k := k) e ≤
      RingHom.ker
        (MvPolynomial.PowerQuotient.zeroEval (σ := σ) (k := k)).toRingHom)

/- The quotient augmentation. -/
#check
  (MvPolynomial.PowerQuotient.augmentationAlgHom (σ := σ) (k := k) e :
    MvPolynomial.PowerQuotient.Quotient (σ := σ) (k := k) e →ₐ[k] k)

/- The representative-level augmentation formula. -/
#check
  (MvPolynomial.PowerQuotient.augmentation_apply_quotientMap
      (σ := σ) (k := k) e :
    ∀ f : MvPolynomial σ k,
      MvPolynomial.PowerQuotient.augmentationAlgHom (σ := σ) (k := k) e
          (MvPolynomial.PowerQuotient.quotientMap (σ := σ) (k := k) e f) =
        MvPolynomial.PowerQuotient.zeroEval (σ := σ) (k := k) f)

/- The map from degree zero to the coefficient ring. -/
#check
  (MvPolynomial.PowerQuotient.degreeZeroToBase (σ := σ) (k := k) e :
    MvPolynomial.PowerQuotient.grading (σ := σ) (k := k) e 0 →ₗ[k] k)

/- The constant-polynomial map into degree zero. -/
#check
  (MvPolynomial.PowerQuotient.baseToDegreeZero (σ := σ) (k := k) e :
    k →ₗ[k] MvPolynomial.PowerQuotient.grading (σ := σ) (k := k) e 0)

/- One inverse law for the degree-zero maps. -/
#check
  (MvPolynomial.PowerQuotient.degreeZeroToBase_baseToDegreeZero
      (σ := σ) (k := k) e :
    (MvPolynomial.PowerQuotient.degreeZeroToBase (σ := σ) (k := k) e).comp
        (MvPolynomial.PowerQuotient.baseToDegreeZero (σ := σ) (k := k) e) =
      LinearMap.id)

/- The other inverse law for the degree-zero maps. -/
#check
  (MvPolynomial.PowerQuotient.baseToDegreeZero_degreeZeroToBase
      (σ := σ) (k := k) e :
    (MvPolynomial.PowerQuotient.baseToDegreeZero (σ := σ) (k := k) e).comp
        (MvPolynomial.PowerQuotient.degreeZeroToBase (σ := σ) (k := k) e) =
      LinearMap.id)

/- The natural-degree-zero linear equivalence. -/
#check
  (MvPolynomial.PowerQuotient.degreeZeroLinearEquiv (σ := σ) (k := k) e :
    MvPolynomial.PowerQuotient.grading (σ := σ) (k := k) e 0 ≃ₗ[k] k)

/- The representative-level formula for the degree-zero equivalence. -/
#check
  (MvPolynomial.PowerQuotient.degreeZeroLinearEquiv_apply_of_representative
      (σ := σ) (k := k) e :
    ∀ (x : MvPolynomial.PowerQuotient.grading (σ := σ) (k := k) e 0)
      (y : MvPolynomial.standardGrading σ k 0),
      (MvPolynomial.PowerQuotient.quotientMap (σ := σ) (k := k) e y :
          MvPolynomial.PowerQuotient.Quotient (σ := σ) (k := k) e) = x →
        MvPolynomial.PowerQuotient.degreeZeroLinearEquiv
            (σ := σ) (k := k) e x =
          MvPolynomial.constantCoeff y.1)

/- The integer-indexed quotient grading. -/
#check
  (MvPolynomial.PowerQuotient.integerGrading (σ := σ) (k := k) e :
    ℤ → Submodule k
      (MvPolynomial.PowerQuotient.Quotient (σ := σ) (k := k) e))

/- The canonical graded scalar action on the quotient grading. -/
#check
  (MvPolynomial.PowerQuotient.instGradedSMulGrading
      (σ := σ) (k := k) e :
    SetLike.GradedSMul (MvPolynomial.standardGrading σ k)
      (MvPolynomial.PowerQuotient.grading (σ := σ) (k := k) e))

end AlgebraicClosure

section AssociatedModuleClosure

variable {R : Type u} {A M : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M]
variable (𝒜 : ℕ → Submodule R A) (ℳ : ℤ → Submodule R M)
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedAlgebra 𝒜]

/- The associated module sheaf in the generalized two-universe interface. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.sheaf 𝒜 ℳ :
    (AlgebraicGeometry.Proj 𝒜).Modules)

/- The generic map from degree zero to global sections. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜 ℳ :
    ℳ 0 →ₗ[𝒜 0]
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.AssociatedModule.degreeZeroRingHom 𝒜)).obj
          (AlgebraicGeometry.Proj.AssociatedModule.sectionModule 𝒜 ℳ ⊤))

/- The generic vanishing criterion for an associated module sheaf. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.sheaf_isZero_of_irrelevant_pow_le_annihilator
      𝒜 ℳ :
    ∀ n : ℕ,
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ n ≤ Module.annihilator A M →
        CategoryTheory.Limits.IsZero
          (AlgebraicGeometry.Proj.AssociatedModule.sheaf 𝒜 ℳ))

variable (x : AlgebraicGeometry.Proj 𝒜)
variable {U V : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V)

/- Naturality of point evaluation in the generic associated-module construction. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.pointSkyscraperApp_naturality
      𝒜 ℳ x i :
    (AlgebraicGeometry.Proj.AssociatedModule.presheaf 𝒜 ℳ).map i ≫
        (ModuleCat.restrictScalars
          ((AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj.map i).hom).map
            (AlgebraicGeometry.Proj.AssociatedModule.pointSkyscraperApp 𝒜 ℳ x V) =
      AlgebraicGeometry.Proj.AssociatedModule.pointSkyscraperApp 𝒜 ℳ x U ≫
        PresheafOfModules.Skyscraper.map (AlgebraicGeometry.Proj 𝒜).presheaf x
          (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
            (AlgebraicGeometry.Proj.AssociatedModule.atPoint 𝒜 ℳ x)) i)

end AssociatedModuleClosure

section ProjectiveClosure

variable {σ : Type u} {k : Type v} [CommRing k] [Fintype σ]
variable (e : ℕ+)

/- The irrelevant-ideal annihilator estimate. -/
#check
  (AlgebraicGeometry.Proj.PowerQuotient.irrelevant_pow_le_annihilator
      (σ := σ) (k := k) e :
    (HomogeneousIdeal.irrelevant (MvPolynomial.standardGrading σ k)).toIdeal ^
        (Fintype.card σ * ((e : ℕ) - 1) + 1) ≤
      Module.annihilator (MvPolynomial σ k)
        (MvPolynomial.PowerQuotient.Quotient (σ := σ) (k := k) e))

/- The associated sheaf of the coordinate-power quotient. -/
#check
  (AlgebraicGeometry.Proj.PowerQuotient.associatedSheaf
      (σ := σ) (k := k) e :
    (AlgebraicGeometry.Proj (MvPolynomial.standardGrading σ k)).Modules)

/- The canonical degree-zero section map of the coordinate-power quotient. -/
#check
  (AlgebraicGeometry.Proj.PowerQuotient.degreeZeroSectionMap
      (σ := σ) (k := k) e :
    MvPolynomial.PowerQuotient.integerGrading (σ := σ) (k := k) e 0 →ₗ[
        MvPolynomial.standardGrading σ k 0]
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.AssociatedModule.degreeZeroRingHom
          (MvPolynomial.standardGrading σ k))).obj
            (AlgebraicGeometry.Proj.AssociatedModule.sectionModule
              (MvPolynomial.standardGrading σ k)
              (MvPolynomial.PowerQuotient.integerGrading (σ := σ) (k := k) e) ⊤))

end ProjectiveClosure
