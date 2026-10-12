/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Torsion.Basic
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

@[expose] public section

/-!
# Exact Associated Primes in Exact Sequences

This module supplies the exact-sequence API for the exact-annihilator associated primes
`associatedPrimesOfModule`.  It parallels mathlib's `associatedPrimes` API without imposing a
Noetherian hypothesis.
-/

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']
variable {M'' : Type x} [AddCommGroup M''] [Module R M'']
variable {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}

namespace associatedPrimesOfModule

/-- An injective linear map sends exact associated primes into those of its target. -/
@[stacks 02M3 "(1)"]
theorem subset_of_injective (hf : Function.Injective f) :
    associatedPrimesOfModule R M ⊆ associatedPrimesOfModule R M' := by
  intro p hp
  change Ideal.IsAssociatedToModule R M p at hp
  change Ideal.IsAssociatedToModule R M' p
  rcases hp with ⟨hpPrime, m, hm⟩
  refine ⟨hpPrime, f m, ?_⟩
  rw [Ideal.torsionOf_map_eq_of_injective hf]
  exact hm

/-- In an exact sequence `0 → M → M' → M''`, every exact associated prime of `M'` comes from
`M` or `M''`. -/
@[stacks 02M3 "(2)"]
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    associatedPrimesOfModule R M' ⊆
      associatedPrimesOfModule R M ∪ associatedPrimesOfModule R M'' := by
  intro p hp
  change Ideal.IsAssociatedToModule R M' p at hp
  rcases hp with ⟨hpPrime, x, hx⟩
  by_cases h : ∃ a, a ∉ p ∧ ∃ y, f y = a • x
  · rcases h with ⟨a, ha, y, hy⟩
    left
    change Ideal.IsAssociatedToModule R M p
    refine ⟨hpPrime, y, ?_⟩
    ext b
    constructor
    · intro hb
      rw [Ideal.mem_torsionOf_iff]
      apply hf
      have hbx : b • x = 0 :=
        (Ideal.mem_torsionOf_iff x b).mp (hx ▸ hb)
      calc
        f (b • y) = b • f y := f.map_smul b y
        _ = b • (a • x) := by rw [hy]
        _ = a • (b • x) := by rw [smul_smul, smul_smul, mul_comm]
        _ = 0 := by rw [hbx, smul_zero]
        _ = f 0 := (f.map_zero).symm
    · intro hb
      have hby : b • y = 0 := (Ideal.mem_torsionOf_iff y b).mp hb
      have hmulx : (b * a) • x = 0 := by
        calc
          (b * a) • x = b • (a • x) := mul_smul b a x
          _ = b • f y := by rw [hy]
          _ = f (b • y) := (f.map_smul b y).symm
          _ = f 0 := by rw [hby]
          _ = 0 := f.map_zero
      have hba : b * a ∈ p := by
        rw [hx]
        exact (Ideal.mem_torsionOf_iff x (b * a)).mpr hmulx
      exact (hpPrime.mem_or_mem hba).resolve_right ha
  · right
    change Ideal.IsAssociatedToModule R M'' p
    refine ⟨hpPrime, g x, ?_⟩
    ext b
    constructor
    · intro hb
      rw [Ideal.mem_torsionOf_iff]
      have hbx : b • x = 0 :=
        (Ideal.mem_torsionOf_iff x b).mp (hx ▸ hb)
      calc
        b • g x = g (b • x) := (g.map_smul b x).symm
        _ = g 0 := by rw [hbx]
        _ = 0 := g.map_zero
    · intro hb
      have hgb : b • g x = 0 := (Ideal.mem_torsionOf_iff (g x) b).mp hb
      have hker : b • x ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker]
        simpa using hgb
      rw [hfg.linearMap_ker_eq] at hker
      rcases hker with ⟨y, hy⟩
      by_contra hbnot
      exact h ⟨b, hbnot, y, hy⟩

/-- Exact associated primes turn binary direct sums into unions. -/
@[stacks 02M3 "(3)"]
theorem prod :
    associatedPrimesOfModule R (M × M') =
      associatedPrimesOfModule R M ∪ associatedPrimesOfModule R M' :=
  (subset_union_of_exact LinearMap.inl_injective .inl_snd).antisymm <|
    Set.union_subset_iff.mpr
      ⟨subset_of_injective LinearMap.inl_injective,
        subset_of_injective LinearMap.inr_injective⟩

end associatedPrimesOfModule

end
