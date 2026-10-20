module

public import ReasLib.Algebra.CentralSimple.SimpleModule.Uniqueness
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

/-! # Direct sum decomposition of finite modules

This file establishes that every finite module over a simple Artinian ring decomposes as a
finite direct sum of copies of the unique simple module, and that two such modules are
isomorphic if and only if they have equal `k`-dimension.
-/

universe u v w w'

section FiniteFunctionRanks

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
private theorem fin_succ_fun_nonempty_linearEquiv (n : ℕ) :
    Nonempty ((Fin (n + 1) → V) ≃ₗ[k] V × (Fin n → V)) := by
  refine ⟨?_⟩
  refine
    { toFun := fun f ↦ (f 0, fun i ↦ f i.succ)
      invFun := fun p i ↦ Fin.cases p.1 p.2 i
      map_add' := fun f g ↦ rfl
      map_smul' := fun c f ↦ rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    ext i
    cases i using Fin.cases with
    | zero =>
        rfl
    | succ i =>
        rfl
  · intro p
    rcases p with ⟨x, f⟩
    rfl

private theorem finrank_fin_fun (n : ℕ) :
    Module.finrank k (Fin n → V) = n * Module.finrank k V := by
  induction n with
  | zero =>
      simp [Module.finrank_pi_fintype]
  | succ n ih =>
      obtain ⟨e⟩ := fin_succ_fun_nonempty_linearEquiv (k := k) (V := V) n
      calc
        Module.finrank k (Fin (n + 1) → V) = Module.finrank k (V × (Fin n → V)) :=
          e.finrank_eq
        _ = Module.finrank k V + Module.finrank k (Fin n → V) := Module.finrank_prod
        _ = Module.finrank k V + n * Module.finrank k V := by rw [ih]
        _ = n * Module.finrank k V + Module.finrank k V := by rw [Nat.add_comm]
        _ = (n + 1) * Module.finrank k V := by rw [Nat.add_mul, one_mul]

end FiniteFunctionRanks

namespace IsSimpleModule

section

open LinearMap

variable {k : Type u} {A : Type v}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]

variable {M : Type w} {N : Type w'}
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]

/-- Every finite left `A`-module is a finite direct sum of copies of a fixed
simple left `A`-module; here `Fin n → M` represents the finite direct sum of `n` copies
of `M`. -/
@[stacks 074E]
theorem nonempty_linearEquiv_fin_fun
    {A : Type v} [Ring A] [IsSimpleRing A] [IsArtinianRing A] {M : Type w} {N : Type w'}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsSimpleModule A M] [Module.Finite A N] :
    ∃ n : ℕ, Nonempty (N ≃ₗ[A] (Fin n → M)) := by
  let _ : IsSemisimpleRing A :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  let hNM : IsIsotypicOfType A N M := fun S _ ↦ by
    let _ : IsSimpleModule A S := ‹_›
    exact IsSimpleModule.nonempty_linearEquiv
  exact hNM.linearEquiv_fun

variable [Module k M] [IsScalarTower k A M]
variable [Module k N] [IsScalarTower k A N]

/-- Two finite left `A`-modules are isomorphic exactly when they have the same
dimension over `k`. -/
@[stacks 074E]
theorem linearEquiv_iff_finrank_eq [IsSimpleModule A M] [Module.Finite A M]
    [Module.Finite A N] :
    Nonempty (M ≃ₗ[A] N) ↔ Module.finrank k M = Module.finrank k N := by
  constructor
  · rintro ⟨e⟩
    simpa using (e.restrictScalars k).finrank_eq
  · intro hMN
    let _ : Nontrivial A := inferInstance
    let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
    obtain ⟨S, hS⟩ := FiniteDimensional.exists_simpleSubmodule_regular (k := k) (A := A)
    let _ : IsSimpleModule A ↥S := hS
    let _ : Nontrivial ↥S := IsSimpleModule.nontrivial A ↥S
    let _ : FiniteDimensional k ↥S :=
      IsSimpleModule.finiteDimensional (k := k) (A := A) (M := ↥S)
    obtain ⟨m, ⟨eM⟩⟩ :=
      nonempty_linearEquiv_fin_fun (A := A) (M := ↥S) (N := M)
    obtain ⟨n, ⟨eN⟩⟩ :=
      nonempty_linearEquiv_fin_fun (A := A) (M := ↥S) (N := N)
    have hM :
        Module.finrank k M = m * Module.finrank k ↥S := by
      calc
        Module.finrank k M = Module.finrank k (Fin m → ↥S) :=
          (eM.restrictScalars k).finrank_eq
        _ = m * Module.finrank k ↥S := finrank_fin_fun (k := k) (V := ↥S) m
    have hN :
        Module.finrank k N = n * Module.finrank k ↥S := by
      calc
        Module.finrank k N = Module.finrank k (Fin n → ↥S) :=
          (eN.restrictScalars k).finrank_eq
        _ = n * Module.finrank k ↥S := finrank_fin_fun (k := k) (V := ↥S) n
    have hSpos : 0 < Module.finrank k ↥S := Module.finrank_pos
    have hmn : m = n := by
      apply Nat.eq_of_mul_eq_mul_left hSpos
      simpa [hM, hN, Nat.mul_comm] using hMN
    subst hmn
    exact ⟨eM.trans eN.symm⟩

end

end IsSimpleModule

end
