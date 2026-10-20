/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Determinant.ProjectiveProperties

@[expose] public section

universe u v w

/- The finite-projective determinant is multiplicative, cyclic at equal local rank,
and compatible with extension of scalars. -/
#check (LinearMap.projectiveDet_comp :
  ∀ {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] (f g : M →ₗ[A] M),
    LinearMap.projectiveDet (f ∘ₗ g) =
      LinearMap.projectiveDet f * LinearMap.projectiveDet g)
#check (LinearMap.projectiveDet_comp_comm :
  ∀ {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] {N : Type w} [AddCommGroup N]
    [Module A N] [Module.Finite A N] [Module.Projective A N]
    (h_rank : ∀ p : PrimeSpectrum A, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (φ : M →ₗ[A] N) (ψ : N →ₗ[A] M),
    LinearMap.projectiveDet (φ ∘ₗ ψ) =
      LinearMap.projectiveDet (ψ ∘ₗ φ))
#check (LinearMap.projectiveDet_baseChange :
  ∀ {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] {A' : Type w} [CommRing A']
    [Algebra A A'] (φ : M →ₗ[A] M),
    LinearMap.projectiveDet (φ.baseChange A') =
      algebraMap A A' (LinearMap.projectiveDet φ))
