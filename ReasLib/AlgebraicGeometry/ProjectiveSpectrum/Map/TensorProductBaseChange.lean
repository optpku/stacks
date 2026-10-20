/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Twist

/-!
# Tensor-product base change of projective spectra

This leaf owns the absolute `Proj` base-change construction for a graded algebra and exposes the
underlying map, cartesian square, and degreewise twist comparison on its natural domain.
-/

@[expose] public section

open AlgebraicGeometry
open Algebra.TensorProduct
open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
variable [Algebra R R'] [Algebra R A]
variable (calA : Nat -> Submodule R A) [GradedAlgebra calA]

/-- The grading on the tensor-product base change of a graded `R`-algebra. -/
abbrev tensorProductBaseChangeGrading : Nat -> Submodule R' (R' ⊗[R] A) :=
  fun n => (calA n).baseChange R'

variable {PcalA : ProjTwistPresentation calA}
variable {PcalB : ProjTwistPresentation
  (tensorProductBaseChangeGrading calA : Nat -> Submodule R' (R' ⊗[R] A))}

omit [GradedAlgebra calA] in
/-- The canonical map into a tensor-product base change preserves each homogeneous piece. -/
theorem tensorProductBaseChangePsi_map_mem
    (i : Nat) (x : A) (hx : x ∈ calA i) :
    (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := A)) x ∈
      tensorProductBaseChangeGrading calA i := by
  change (1 : R') ⊗ₜ[R] x ∈ (calA i).baseChange R'
  exact Submodule.tmul_mem_baseChange_of_mem (A := R') (p := calA i) (1 : R') hx

/-- The canonical graded map from a graded algebra to its tensor-product base change. -/
abbrev tensorProductBaseChangePsi :
    calA →+*ᵍ (tensorProductBaseChangeGrading calA : Nat -> Submodule R' (R' ⊗[R] A)) where
  __ := (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := A)).toRingHom
  map_mem := fun {i x} hx => tensorProductBaseChangePsi_map_mem calA i x hx

/-- The `ProjMap` induced by tensor-product base change. -/
abbrev tensorProductBaseChangeProjMap
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation
      (tensorProductBaseChangeGrading calA : Nat -> Submodule R' (R' ⊗[R] A))) :
    ProjMap PcalA PcalB (tensorProductBaseChangePsi calA) :=
  projMap PcalA PcalB (tensorProductBaseChangePsi calA)

/-- The structure morphism from the projective spectrum of a graded `R`-algebra to `Spec R`. -/
abbrev projToSpecBase :
    Proj calA ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero calA ≫ Spec.map (CommRingCat.ofHom (algebraMap R (calA 0)))

/-- The structure morphism from the base-changed projective spectrum to `Spec R'`. -/
abbrev tensorProductBaseChangeProjToSpecBase :
    Proj (tensorProductBaseChangeGrading calA : Nat -> Submodule R' (R' ⊗[R] A)) ⟶
      Spec (CommRingCat.of R') :=
  Proj.toSpecZero (tensorProductBaseChangeGrading calA : Nat -> Submodule R' (R' ⊗[R] A)) ≫
    Spec.map
      (CommRingCat.ofHom
        (algebraMap R' ((tensorProductBaseChangeGrading calA : Nat -> Submodule R' (R' ⊗[R] A)) 0)))

/-- Tensor-product base change has full natural `Proj` map domain. -/
theorem projMapDomain_tensorProductBaseChange_eq_top :
    projMapDomain
      (tensorProductBaseChangePsi calA :
        calA →+*ᵍ (tensorProductBaseChangeGrading calA : Nat -> Submodule R' (R' ⊗[R] A))) = ⊤ := sorry

/-- The tensor-product base-change square on the natural `Proj` map domain is cartesian. -/
theorem projMap_tensorProductBaseChange_isPullback :
    CategoryTheory.IsPullback
      (tensorProductBaseChangeProjMap calA PcalA PcalB).map
      ((projMapDomain
          (tensorProductBaseChangePsi calA :
            calA →+*ᵍ
              (tensorProductBaseChangeGrading calA : Nat -> Submodule R' (R' ⊗[R] A)))).ι ≫
        tensorProductBaseChangeProjToSpecBase calA)
      (projToSpecBase calA)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := sorry

/-- The degreewise twist comparison on the natural `Proj` map domain is an isomorphism. -/
theorem instIsIso_theta_tensorProductBaseChange
    (n : Int) :
    IsIso ((tensorProductBaseChangeProjMap calA PcalA PcalB).theta n) := sorry

end

end AlgebraicGeometry
