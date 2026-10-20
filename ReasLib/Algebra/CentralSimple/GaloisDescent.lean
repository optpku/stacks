/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Splitting.TFAE
public import ReasLib.Algebra.CentralSimple.SkolemNoether
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Degree
public import ReasLib.Algebra.GroupCohomology.ProjectiveLinearBoundary
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

universe u v w

open scoped TensorProduct MatrixGroups

namespace CSA

variable {K : Type u} [Field K]

/-- A positive matrix size in a splitting over the canonical separable closure. -/
noncomputable def separableSplittingSize (A : CSA.{u, w} K) : ℕ+ :=
  Classical.choose
    ((A.isSplitBy_iff_exists_pnat (SeparableClosure K)).mp A.isSplitBy_separableClosure)

/-- The positive matrix size of a separable splitting equals the degree of the algebra. -/
theorem separableSplittingSize_eq_degree (A : CSA.{u, w} K) :
    (A.separableSplittingSize : ℕ) = A.degree := sorry

/-- A matrix splitting of a central simple algebra over any separable closure. -/
noncomputable def separableSplittingEquiv (A : CSA.{u, w} K)
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] :
    A.baseChange Ksep ≃ₐ[Ksep]
      Matrix (Fin A.separableSplittingSize) (Fin A.separableSplittingSize) Ksep :=
  let splitting := Classical.choice
    (Classical.choose_spec
      ((A.isSplitBy_iff_exists_pnat (SeparableClosure K)).mp A.isSplitBy_separableClosure))
  let closureEquiv := IsSepClosure.equiv K Ksep (SeparableClosure K)
  let tensorEquiv := Algebra.TensorProduct.congr closureEquiv (AlgEquiv.refl : A ≃ₐ[K] A)
  let matrixEquiv := closureEquiv.symm.toRingEquiv.mapMatrix
  AlgEquiv.ofRingEquiv
    (f := tensorEquiv.toRingEquiv.trans (splitting.toRingEquiv.trans matrixEquiv))
    (fun scalar ↦
      (congrArg matrixEquiv
        ((congrArg splitting
          (Algebra.TensorProduct.map_tmul closureEquiv.toAlgHom (AlgHom.id K A) scalar 1)).trans
            (splitting.commutes (closureEquiv scalar)))).trans
        ((Matrix.diagonal_map (map_zero closureEquiv.symm)).trans
          (congrArg Matrix.diagonal
            (funext (fun _ ↦ closureEquiv.symm_apply_apply scalar)))))

variable (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
variable (A : CSA.{u, w} K) (n : ℕ+)
variable (e : A.baseChange Ksep ≃ₐ[Ksep] Matrix (Fin n) (Fin n) Ksep)

/-- Semilinear tensor descent followed by inverse entrywise descent fixes the scalar matrices. -/
theorem descentAutomorphism_commutes (σ : Gal(Ksep / K)) (scalar : Ksep) :
    (((σ.symm.toRingEquiv.mapMatrix).trans e.symm.toRingEquiv).trans
      ((Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[K] A)).toRingEquiv.trans
        e.toRingEquiv)) (algebraMap Ksep (Matrix (Fin n) (Fin n) Ksep) scalar) =
      algebraMap Ksep (Matrix (Fin n) (Fin n) Ksep) scalar := sorry

/-- The linear matrix automorphism obtained from a splitting and semilinear Galois descent. -/
noncomputable def descentAutomorphism (σ : Gal(Ksep / K)) :
    Matrix (Fin n) (Fin n) Ksep ≃ₐ[Ksep] Matrix (Fin n) (Fin n) Ksep :=
  AlgEquiv.ofRingEquiv
    (f := ((σ.symm.toRingEquiv.mapMatrix).trans e.symm.toRingEquiv).trans
      ((Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[K] A)).toRingEquiv.trans
        e.toRingEquiv))
    (descentAutomorphism_commutes Ksep A n e σ)

/-- A fixed implementing matrix for an automorphism of a full matrix algebra. -/
noncomputable def matrixInnerLift
    (automorphism : Matrix (Fin n) (Fin n) Ksep ≃ₐ[Ksep] Matrix (Fin n) (Fin n) Ksep) :
    GL (Fin n) Ksep :=
  Classical.choose (CSA.matrix_algEquiv_isInner n automorphism)

/-- The chosen implementing matrix realizes its automorphism by conjugation. -/
theorem matrixInnerLift_spec
    (automorphism : Matrix (Fin n) (Fin n) Ksep ≃ₐ[Ksep] Matrix (Fin n) (Fin n) Ksep)
    (matrix : Matrix (Fin n) (Fin n) Ksep) :
    automorphism matrix = (matrixInnerLift Ksep n automorphism).val * matrix *
      (matrixInnerLift Ksep n automorphism)⁻¹.val := sorry

/-- The lift of matrix descent obtained by composing descent with a fixed inner-automorphism section. -/
noncomputable def descentLift (σ : Gal(Ksep / K)) : GL (Fin n) Ksep :=
  matrixInnerLift Ksep n (descentAutomorphism Ksep A n e σ)

/-- The projective matrix-valued descent cocycle of a split central simple algebra. -/
noncomputable def descentCocycle (σ : Gal(Ksep / K)) : PGL(n, Ksep) :=
  Matrix.ProjGenLinGroup.mk (descentLift Ksep A n e σ)

/-- Projective matrix descent satisfies the nonabelian Galois one-cocycle identity. -/
theorem descentCocycle_cocycle (σ τ : Gal(Ksep / K)) :
    descentCocycle Ksep A n e (σ * τ) =
      descentCocycle Ksep A n e σ * σ • descentCocycle Ksep A n e τ := sorry

/-- The fixed-section matrix lift of Galois descent is locally constant. -/
theorem descentLift_locallyConstant : IsLocallyConstant (descentLift Ksep A n e) := sorry

/-- The scalar boundary of matrix descent uses
`(lift σ)⁻¹ * lift (σ * τ) * (σ • (lift τ)⁻¹)`. -/
noncomputable def descentBoundary : Gal(Ksep / K) × Gal(Ksep / K) → Ksepˣ :=
  brauerTwoCocycle K n n.pos (descentCocycle Ksep A n e) (descentLift Ksep A n e)
    (descentCocycle_cocycle Ksep A n e) (fun _ ↦ rfl)

/-- The scalar two-cocycle of matrix descent is locally constant with discrete coefficients. -/
theorem descentBoundary_locallyConstant :
    IsLocallyConstant (descentBoundary Ksep A n e) := sorry

end CSA

end
