/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.AffineOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (U : (Spec (.of A)).Opens)

#check (MvPolynomial.standardGrading Unit A :
  ℕ → Submodule A (MvPolynomial Unit A))

#check (AlgebraicGeometry.AffineOpenProj.generatorSet U :
  Set (MvPolynomial Unit A))

#check (AlgebraicGeometry.AffineOpenProj.subalgebra U :
  Subalgebra A (MvPolynomial Unit A))

#check (AlgebraicGeometry.AffineOpenProj.grading U :
  ℕ → Submodule A (AlgebraicGeometry.AffineOpenProj.subalgebra U))

#check (AlgebraicGeometry.AffineOpenProj.instGradedMonoid U :
  SetLike.GradedMonoid (AlgebraicGeometry.AffineOpenProj.grading U))

#check (AlgebraicGeometry.AffineOpenProj.subalgebra_isHomogeneous U :
  (Subalgebra.toSubmodule (AlgebraicGeometry.AffineOpenProj.subalgebra U)).IsHomogeneous
    (MvPolynomial.standardGrading Unit A))

#check (AlgebraicGeometry.AffineOpenProj.decomposition U :
  AlgebraicGeometry.AffineOpenProj.subalgebra U →
    DirectSum ℕ (fun n ↦ AlgebraicGeometry.AffineOpenProj.grading U n))

#check (AlgebraicGeometry.AffineOpenProj.decomposition_add U :
  ∀ x y : AlgebraicGeometry.AffineOpenProj.subalgebra U,
    AlgebraicGeometry.AffineOpenProj.decomposition U (x + y) =
      AlgebraicGeometry.AffineOpenProj.decomposition U x +
        AlgebraicGeometry.AffineOpenProj.decomposition U y)

#check (AlgebraicGeometry.AffineOpenProj.decomposition_smul U :
  ∀ (a : A) (x : AlgebraicGeometry.AffineOpenProj.subalgebra U),
    AlgebraicGeometry.AffineOpenProj.decomposition U (a • x) =
      a • AlgebraicGeometry.AffineOpenProj.decomposition U x)

#check (AlgebraicGeometry.AffineOpenProj.decomposition_one U :
  AlgebraicGeometry.AffineOpenProj.decomposition U 1 = 1)

#check (AlgebraicGeometry.AffineOpenProj.decomposition_mul U :
  ∀ x y : AlgebraicGeometry.AffineOpenProj.subalgebra U,
    AlgebraicGeometry.AffineOpenProj.decomposition U (x * y) =
      AlgebraicGeometry.AffineOpenProj.decomposition U x *
        AlgebraicGeometry.AffineOpenProj.decomposition U y)

#check (AlgebraicGeometry.AffineOpenProj.decompose U :
  AlgebraicGeometry.AffineOpenProj.subalgebra U →ₐ[A]
    DirectSum ℕ (fun n ↦ AlgebraicGeometry.AffineOpenProj.grading U n))

#check (AlgebraicGeometry.AffineOpenProj.coeAlgHom_comp_decompose U :
  (DirectSum.coeAlgHom (fun n ↦ AlgebraicGeometry.AffineOpenProj.grading U n)).comp
      (AlgebraicGeometry.AffineOpenProj.decompose U) =
    AlgHom.id A (AlgebraicGeometry.AffineOpenProj.subalgebra U))

#check (AlgebraicGeometry.AffineOpenProj.decompose_coe U :
  ∀ (n : ℕ) (x : AlgebraicGeometry.AffineOpenProj.grading U n),
    AlgebraicGeometry.AffineOpenProj.decompose U
        (x : AlgebraicGeometry.AffineOpenProj.subalgebra U) =
      DirectSum.of (fun m ↦ AlgebraicGeometry.AffineOpenProj.grading U m) n x)

#check (AlgebraicGeometry.AffineOpenProj.instGradedAlgebra U :
  GradedAlgebra (AlgebraicGeometry.AffineOpenProj.grading U))

#check (AlgebraicGeometry.AffineOpenProj.algebraMap_mem_degreeZero U :
  ∀ a : A, algebraMap A (AlgebraicGeometry.AffineOpenProj.subalgebra U) a ∈
    AlgebraicGeometry.AffineOpenProj.grading U 0)

#check (AlgebraicGeometry.AffineOpenProj.degreeZeroC U :
  A → AlgebraicGeometry.AffineOpenProj.grading U 0)

#check (AlgebraicGeometry.AffineOpenProj.degreeZero_leftInverse U :
  Function.LeftInverse (AlgebraicGeometry.AffineOpenProj.degreeZeroC U)
    (fun p : AlgebraicGeometry.AffineOpenProj.grading U 0 ↦
      MvPolynomial.constantCoeff p.1.1))

#check (AlgebraicGeometry.AffineOpenProj.degreeZeroRingEquiv U :
  AlgebraicGeometry.AffineOpenProj.grading U 0 ≃+* A)

#check (AlgebraicGeometry.AffineOpenProj.degreeZeroAlgebraMap U :
  A →+* AlgebraicGeometry.AffineOpenProj.grading U 0)

#check (AlgebraicGeometry.AffineOpenProj.degreeZeroRingEquiv_symm_apply U :
  ∀ a : A, (AlgebraicGeometry.AffineOpenProj.degreeZeroRingEquiv U).symm a =
    AlgebraicGeometry.AffineOpenProj.degreeZeroAlgebraMap U a)

#check (AlgebraicGeometry.Proj.toSpecZero
    (AlgebraicGeometry.AffineOpenProj.grading U) :
  Proj (AlgebraicGeometry.AffineOpenProj.grading U) ⟶
    Spec (.of (AlgebraicGeometry.AffineOpenProj.grading U 0)))

#check (AlgebraicGeometry.Proj.toSpecZero_base_asIdeal
    (𝒜 := AlgebraicGeometry.AffineOpenProj.grading U) :
  ∀ x : ProjectiveSpectrum (AlgebraicGeometry.AffineOpenProj.grading U),
    ((AlgebraicGeometry.Proj.toSpecZero
      (AlgebraicGeometry.AffineOpenProj.grading U)).base x).asIdeal =
      Ideal.comap
        (algebraMap (AlgebraicGeometry.AffineOpenProj.grading U 0)
          (AlgebraicGeometry.AffineOpenProj.subalgebra U))
        x.asHomogeneousIdeal.toIdeal)

#check (AlgebraicGeometry.AffineOpenProj.toSpec U :
  Proj (AlgebraicGeometry.AffineOpenProj.grading U) ⟶ Spec (.of A))

#check (AlgebraicGeometry.AffineOpenProj.toSpec_preimage_eq_top U :
  AlgebraicGeometry.AffineOpenProj.toSpec U ⁻¹ᵁ U = ⊤)

#check (AlgebraicGeometry.AffineOpenProj.toOpen U :
  Proj (AlgebraicGeometry.AffineOpenProj.grading U) ⟶ U.toScheme)

/- Example 27.8.15: the projective spectrum of the generated graded subalgebra is canonically
isomorphic to the given open subscheme of the affine spectrum. -/
@[stacks 0G5W] #check (AlgebraicGeometry.AffineOpenProj.instIsIsoToOpen U :
  IsIso (AlgebraicGeometry.AffineOpenProj.toOpen U))

#check (AlgebraicGeometry.AffineOpenProj.toOpen_comp_ι U :
  AlgebraicGeometry.AffineOpenProj.toOpen U ≫ U.ι =
    Proj.toSpecZero (AlgebraicGeometry.AffineOpenProj.grading U) ≫
      (Scheme.Spec.mapIso
        ((AlgebraicGeometry.AffineOpenProj.degreeZeroRingEquiv U).toCommRingCatIso.op)).symm.hom)
