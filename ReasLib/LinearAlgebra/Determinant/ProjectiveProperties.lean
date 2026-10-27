/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Determinant.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Free

@[expose] public section

universe u v w

open scoped TensorProduct

noncomputable section

namespace LinearMap

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
  [Module.Finite A M] [Module.Projective A M]
variable {N : Type w} [AddCommGroup N] [Module A N]
  [Module.Finite A N] [Module.Projective A N]

/-- Extend a split finite-free presentation to a new scalar algebra, using the native
coordinate isomorphism for the scalar extension of a finite free module. -/
def SplitFreePresentation.baseChange (p : SplitFreePresentation A M)
    (A' : Type*) [CommRing A'] [Algebra A A'] : SplitFreePresentation A' (A' ⊗[A] M) :=
  let e := Algebra.TensorProduct.equivPiOfFiniteBasis A' (Pi.basisFun A (Fin p.rank))
  { rank := p.rank
    pi := p.pi.baseChange A' ∘ₗ e.symm.toLinearMap
    iota := e.toLinearMap ∘ₗ p.iota.baseChange A'
    pi_comp_iota := by
      have hp : ∀ x : M, p.pi (p.iota x) = x :=
        fun x ↦ congrArg (fun h : M →ₗ[A] M ↦ h x) p.pi_comp_iota
      apply TensorProduct.AlgebraTensorModule.ext
      intro a m
      simp [comp_apply, hp] }

/-- The scalar-extended split lift is the conjugate of the scalar extension of the lift. -/
theorem SplitFreePresentation.baseChange_lift (p : SplitFreePresentation A M)
    (A' : Type*) [CommRing A'] [Algebra A A'] (f : M →ₗ[A] M) :
    let e := Algebra.TensorProduct.equivPiOfFiniteBasis A' (Pi.basisFun A (Fin p.rank))
    (p.baseChange A').lift (f.baseChange A') =
      e.toLinearMap ∘ₗ (p.lift f).baseChange A' ∘ₗ e.symm.toLinearMap := by
  dsimp only [SplitFreePresentation.baseChange, SplitFreePresentation.lift]
  apply LinearMap.ext
  intro x
  simp [baseChange_comp, comp_apply]
  change x = (Algebra.TensorProduct.equivPiOfFiniteBasis A'
    (Pi.basisFun A (Fin p.rank)))
      ((Algebra.TensorProduct.equivPiOfFiniteBasis A'
        (Pi.basisFun A (Fin p.rank))).symm x)
  exact (LinearEquiv.apply_symm_apply _ _).symm

/-- The determinant of finite-projective endomorphisms is multiplicative. -/
theorem projectiveDet_comp (f g : M →ₗ[A] M) :
    projectiveDet (f ∘ₗ g) = projectiveDet f * projectiveDet g := by
  let p := splitFreePresentation A M
  have hp : ∀ x : M, p.pi (p.iota x) = x :=
    fun x ↦ congrArg (fun h : M →ₗ[A] M ↦ h x) p.pi_comp_iota
  have hlift : p.lift (f ∘ₗ g) = p.lift f ∘ₗ p.lift g := by
    apply LinearMap.ext
    intro x
    simp [SplitFreePresentation.lift, hp]
  rw [projectiveDet_of_presentation p, projectiveDet_of_presentation p,
    projectiveDet_of_presentation p, hlift, det_comp]

/-- Rectangular composites have equal determinants when their finite-projective
modules have equal rank at every prime. -/
theorem projectiveDet_comp_comm
    (h_rank : ∀ p : PrimeSpectrum A, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (φ : M →ₗ[A] N) (ψ : N →ₗ[A] M) :
    projectiveDet (φ ∘ₗ ψ) = projectiveDet (ψ ∘ₗ φ) := sorry

/-- The determinant of a finite-projective endomorphism commutes with extension of scalars. -/
theorem projectiveDet_baseChange {A' : Type w} [CommRing A'] [Algebra A A']
    (φ : M →ₗ[A] M) :
    projectiveDet (φ.baseChange A') = algebraMap A A' (projectiveDet φ) := by
  let p := splitFreePresentation A M
  calc
    projectiveDet (φ.baseChange A') =
        LinearMap.det ((p.baseChange A').lift (φ.baseChange A')) :=
      projectiveDet_of_presentation _ _
    _ = LinearMap.det ((p.lift φ).baseChange A') :=
      (congrArg (fun f : (Fin p.rank → A') →ₗ[A'] (Fin p.rank → A') ↦ LinearMap.det f)
        (p.baseChange_lift A' φ)).trans (det_conj _ _)
    _ = algebraMap A A' (LinearMap.det (p.lift φ)) := det_baseChange _
    _ = algebraMap A A' (projectiveDet φ) :=
      congrArg (algebraMap A A') (projectiveDet_of_presentation p φ).symm

end LinearMap
