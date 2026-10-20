/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w

namespace Module.FinitePresentation

/-- A linear map between finitely presented modules lifts to compatible linear maps between
any chosen finite free presentations, making both squares commute. -/
@[stacks 0GNP]
theorem existsPresentationLift
    {A : Type u} [Ring A]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [Module.FinitePresentation A M] [Module.FinitePresentation A N]
    (m_M n_M m_N n_N : ℕ)
    (φ_M : (Fin m_M → A) →ₗ[A] (Fin n_M → A))
    (π_M : (Fin n_M → A) →ₗ[A] M)
    (φ_N : (Fin m_N → A) →ₗ[A] (Fin n_N → A))
    (π_N : (Fin n_N → A) →ₗ[A] N)
    (h_M_exact : Function.Exact φ_M π_M)
    (h_M_surjective : Function.Surjective π_M)
    (h_N_exact : Function.Exact φ_N π_N)
    (h_N_surjective : Function.Surjective π_N)
    (f : M →ₗ[A] N) :
    ∃ ψ_f : (Fin m_M → A) →ₗ[A] (Fin m_N → A),
      ∃ χ_f : (Fin n_M → A) →ₗ[A] (Fin n_N → A),
        χ_f.comp φ_M = φ_N.comp ψ_f ∧
          f.comp π_M = π_N.comp χ_f := sorry

end Module.FinitePresentation
