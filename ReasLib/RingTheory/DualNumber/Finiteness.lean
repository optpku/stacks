/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Algebra.Polynomial.Div

@[expose] public section

/-!
# Finiteness of the dual-number extension

The dual numbers form a finite and finitely presented algebra over their base ring.
-/

universe u

open scoped DualNumber

namespace DualNumber

variable (R : Type u)

section Semiring

variable [CommSemiring R]

/-- The dual numbers are finite as a module over the base ring. -/
instance finite : Module.Finite R R[ε] := by
  classical
  rw [Module.finite_def]
  let s : Finset R[ε] := {(1 : R[ε]), ε}
  refine ⟨s, ?_⟩
  apply top_unique
  intro x _
  have h_one : (1 : R[ε]) ∈ Submodule.span R (s : Set R[ε]) :=
    Submodule.subset_span (by simp [s])
  have h_eps : (ε : R[ε]) ∈ Submodule.span R (s : Set R[ε]) :=
    Submodule.subset_span (by simp [s])
  rw [← x.inl_fst_add_inr_snd_eq]
  apply Submodule.add_mem
  · simpa [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl] using
      Submodule.smul_mem (Submodule.span R (s : Set R[ε])) x.fst h_one
  · rw [DualNumber.inr_eq_smul_eps]
    exact Submodule.smul_mem (Submodule.span R (s : Set R[ε])) x.snd h_eps

end Semiring

section Ring

variable [CommRing R]

private theorem aeval_eps_eq_coeff_zero_add_coeff_one_eps (p : Polynomial R) :
    Polynomial.aeval (ε : R[ε]) p =
      (⟨p.coeff 0, p.coeff 1⟩ : R[ε]) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      ext <;> simp
  | monomial n a =>
      obtain _ | n := n
      · ext <;>
          simp [TrivSqZeroExt.algebraMap_eq_inl]
      obtain _ | n := n
      · ext <;>
          simp [Polynomial.aeval_monomial, TrivSqZeroExt.algebraMap_eq_inl]
      · have hcoeff :
            (Polynomial.monomial (Nat.succ (Nat.succ n)) a).coeff 1 = 0 :=
          Polynomial.coeff_monomial_of_ne a (Nat.succ_succ_ne_one n).symm
        ext <;>
          simp [Polynomial.aeval_monomial, TrivSqZeroExt.algebraMap_eq_inl, pow_succ, hcoeff]

/-- The dual numbers are finitely presented as an algebra over the base ring. -/
instance finitePresentation : Algebra.FinitePresentation R R[ε] := by
  let f : Polynomial R →ₐ[R] R[ε] := Polynomial.aeval (ε : R[ε])
  have hf : Function.Surjective f := by
    intro x
    refine ⟨Polynomial.C x.fst + Polynomial.C x.snd * Polynomial.X, ?_⟩
    apply TrivSqZeroExt.ext <;>
      simp [f, TrivSqZeroExt.algebraMap_eq_inl]
  have hker : RingHom.ker f.toRingHom =
      Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial R)) := by
    ext p
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · intro hp
      change Polynomial.aeval (ε : R[ε]) p = 0 at hp
      rw [aeval_eps_eq_coeff_zero_add_coeff_one_eps R p] at hp
      have h0 : p.coeff 0 = 0 := by
        simpa using congrArg TrivSqZeroExt.fst hp
      have h1 : p.coeff 1 = 0 := by
        simpa using congrArg TrivSqZeroExt.snd hp
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hd) with rfl | rfl
      · exact h0
      · exact h1
    · rintro ⟨q, hq⟩
      rw [hq]
      simp [f]
  apply Algebra.FinitePresentation.of_surjective hf
  rw [hker]
  exact Submodule.fg_span_singleton (Polynomial.X ^ 2)

end Ring

end DualNumber
