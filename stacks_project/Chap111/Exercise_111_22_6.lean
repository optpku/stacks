/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.ProjectiveProperties
public import ReasLib.LinearAlgebra.Determinant.ProjectiveProperties
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Exercise 111.22.6

The trace and determinant of an endomorphism of a finite locally free module are
`LinearMap.FiniteProjective.trace` and `LinearMap.projectiveDet`. Functoriality in the
triple `(A, M, φ)` is compatibility with extension of scalars.

@stack 02DU
-/

universe u v w

open LinearMap

variable {A : Type u} {A' : Type v} {M : Type w} {N : Type w}
  [CommRing A] [CommRing A'] [Algebra A A']
  [AddCommGroup M] [Module A M] [Module.FiniteLocallyFree A M]
  [AddCommGroup N] [Module A N] [Module.FiniteLocallyFree A N]

/- Exercise 111.22.6 (1): construct Trace and det of an endomorphism of a finite
locally free module, functorially in the triple `(A, M, φ)`. -/
@[stacks 02DU] #check (LinearMap.FiniteProjective.trace : (M →ₗ[A] M) →ₗ[A] A)
#check (LinearMap.projectiveDet : (M →ₗ[A] M) → A)
#check (LinearMap.FiniteProjective.trace_baseChange :
  ∀ (φ : M →ₗ[A] M),
    LinearMap.FiniteProjective.trace (φ.baseChange A') =
      algebraMap A A' (LinearMap.FiniteProjective.trace φ))
#check (LinearMap.projectiveDet_baseChange :
  ∀ (φ : M →ₗ[A] M),
    LinearMap.projectiveDet (φ.baseChange A') = algebraMap A A' (LinearMap.projectiveDet φ))

/- Exercise 111.22.6 (2): Trace(φ ∘ₗ ψ) = Trace(ψ ∘ₗ φ) for finite
locally free modules; determinant cyclicity also requires
`∀ p, Module.rankAtStalk M p = Module.rankAtStalk N p`. -/
@[stacks 02DU]
#check (LinearMap.FiniteProjective.trace_comp_comm :
  ∀ (φ : M →ₗ[A] N) (ψ : N →ₗ[A] M),
    LinearMap.FiniteProjective.trace (φ ∘ₗ ψ) =
      LinearMap.FiniteProjective.trace (ψ ∘ₗ φ))
#check (LinearMap.projectiveDet_comp_comm :
  (∀ p : PrimeSpectrum A, Module.rankAtStalk M p = Module.rankAtStalk N p) →
    ∀ (φ : M →ₗ[A] N) (ψ : N →ₗ[A] M),
      LinearMap.projectiveDet (φ ∘ₗ ψ) = LinearMap.projectiveDet (ψ ∘ₗ φ))

/- Exercise 111.22.6 (3): Trace is an `A`-linear map `End_A(M) → A`, and det is
multiplicative. -/
@[stacks 02DU]
#check (LinearMap.FiniteProjective.trace : (M →ₗ[A] M) →ₗ[A] A)
#check (LinearMap.projectiveDet_comp :
  ∀ f g : M →ₗ[A] M,
    LinearMap.projectiveDet (f ∘ₗ g) = LinearMap.projectiveDet f * LinearMap.projectiveDet g)
