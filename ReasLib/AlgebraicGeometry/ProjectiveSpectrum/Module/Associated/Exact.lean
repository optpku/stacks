/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Functorial

/-!
# Exactness of sheaves associated to graded modules

Exact pairs of degree-preserving maps of graded modules remain exact after homogeneous
localization at every projective point and after passing to the associated module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.AssociatedModule

variable {A M N P : Type u} [CommRing A]
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable [AddCommGroup P] [Module A P]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
variable (calP : ℤ → Submodule ℤ P)
variable [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
variable [DirectSum.Decomposition calP]
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ]
variable [SetLike.GradedSMul 𝒜 calP]

/-- Exactness of a pair of degree-preserving maps is preserved by homogeneous localization at a
projective point. -/
theorem atPointMap_exact (φ : M →ₗ[A] N) (ψ : N →ₗ[A] P)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (hψ : ∀ i : ℤ, Set.MapsTo ψ (ℵ i) (calP i))
    (hExact : Function.Exact φ ψ) (x : AlgebraicGeometry.Proj 𝒜) :
    Function.Exact (atPointMap 𝒜 ℳ ℵ φ hφ x) (atPointMap 𝒜 ℵ calP ψ hψ x) := sorry

/-- The short complex of associated sheaves induced by an exact pair of degree-preserving
module maps. -/
noncomputable def mapShortComplex (φ : M →ₗ[A] N) (ψ : N →ₗ[A] P)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (hψ : ∀ i : ℤ, Set.MapsTo ψ (ℵ i) (calP i))
    (hExact : Function.Exact φ ψ) :
    ShortComplex (AlgebraicGeometry.Proj 𝒜).Modules where
  X₁ := sheaf 𝒜 ℳ
  X₂ := sheaf 𝒜 ℵ
  X₃ := sheaf 𝒜 calP
  f := map 𝒜 ℳ ℵ φ hφ
  g := map 𝒜 ℵ calP ψ hψ
  zero := by
    rw [← map_comp 𝒜 ℳ ℵ calP φ ψ hφ hψ]
    let compMap : { f : M →ₗ[A] P // ∀ i : ℤ, Set.MapsTo f (ℳ i) (calP i) } :=
      ⟨ψ.comp φ, fun i ↦ (hψ i).comp (hφ i)⟩
    let zeroMap : { f : M →ₗ[A] P // ∀ i : ℤ, Set.MapsTo f (ℳ i) (calP i) } :=
      ⟨0, fun i _ _ ↦ (calP i).zero_mem⟩
    have hMaps : compMap = zeroMap := Subtype.ext hExact.linearMap_comp_eq_zero
    change map 𝒜 ℳ calP compMap.1 compMap.2 = 0
    rw [hMaps]
    exact map_zero 𝒜 ℳ calP

/-- Every exact pair of degree-preserving graded-module maps induces an exact short complex of
associated module sheaves. -/
theorem map_exact (φ : M →ₗ[A] N) (ψ : N →ₗ[A] P)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (hψ : ∀ i : ℤ, Set.MapsTo ψ (ℵ i) (calP i))
    (hExact : Function.Exact φ ψ) :
    (mapShortComplex 𝒜 ℳ ℵ calP φ ψ hφ hψ hExact).Exact := sorry

end AlgebraicGeometry.Proj.AssociatedModule
