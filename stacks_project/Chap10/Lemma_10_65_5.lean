/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Ideal.AssociatedPrime.BaseChange.Flat.Contraction
public import stacks_project.Chap10.Lemma_10_65_3
import StacksCheckRecall

/-!
@stack 05C2
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TensorProduct.AlgebraTensorModule
open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/- Domain triage:
* primary domain: associated primes under flat base change along `R → S`;
* source-facing layer: the chapter owner `relativeAssassin R S N` together with the textbook
  exact-annihilator set `associatedPrimesOfModule`;
* core/canonical layer: mathlib's Noetherian owner `associatedPrimes`;
* bridge/view: the contraction description of the fiberwise union coming from Lemma 10.65.1 and
  Remark 10.18.5.

This item stays at the source-facing layer. The Noetherian equality is stated for
`associatedPrimesOfModule`, and any owner-form restatement via `associatedPrimes` belongs in a
later bridge file.
-/

@[stacks 05C2 "flat prime-quotient contraction"]
#check (associatedPrimesOfModule.BaseChange.Flat.under_eq_of_mem_quotient
  (R := R) (S := S) (N := N) :
    ∀ [Module.Flat R N] {p : Ideal R} [p.IsPrime] {q : Ideal S},
      q ∈ associatedPrimesOfModule S
          (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) →
        q.under R = p)

-- Proof sketch: rewrite the fiberwise union from the source as
-- `relativeAssassin R S N ∩ {q | q.asIdeal.under R ∈ associatedPrimesOfModule R M}` using
-- Lemma 10.65.1 together with the fiber-spectrum identification from Remark 10.18.5, then apply
-- Lemma 10.65.3(1) to the contracted prime quotient modules `N / pN`.
/-- Lemma 10.65.5 (1): if `N` is flat over `R`, then every associated prime of a fiber module
`κ(𝔭) ⊗[R] N`, viewed as a prime of `S` by the canonical map
`Spec (κ(𝔭) ⊗[R] S) → Spec S`, for `𝔭 ∈ Ass_R(M)`, is an associated prime of the base-changed
module `M ⊗[R] N`. In Lean the canonically `S`-linear tensor model is written `N ⊗[R] M`. -/
@[stacks 05C2]
theorem fiberAssociatedPrimes_subset_associatedPrimesOfModule_tensorProduct
    [Module.Flat R N] :
    relativeAssassin R S N ∩
        { q : PrimeSpectrum S | q.asIdeal.under R ∈ associatedPrimesOfModule R M } ⊆
      { q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) } := by
  intro q hq
  rcases hq with ⟨hqA, hqM⟩
  -- Rewrite the fiberwise condition through the fixed contracted-prime quotient from Lemma 10.65.1.
  have hqAfin : q ∈ relativeAssassinAfin R S N := by
    rw [← relativeAssassinA_eq_relativeAssassinAfin_of_flat (R := R) (S := S) (N := N)]
    exact hqA
  have hqQuot :
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R)) := by
    simpa using hqAfin
  -- Insert the contracted prime `q ∩ R` into the union from Lemma 10.65.3(1).
  have hqUnion :
      q.asIdeal ∈ ⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) := by
    exact Set.mem_iUnion.mpr ⟨q.asIdeal.under R, Set.mem_iUnion.mpr ⟨hqM, hqQuot⟩⟩
  exact
    associatedPrimesOfModule.BaseChange.Flat.iUnion_quotient_subset
      (R := R) (S := S) (M := M) (N := N) hqUnion

-- Proof sketch: combine the source-facing inclusion above with the Noetherian converse furnished
-- by Lemma 10.65.3(2), again rewriting the fiberwise union through the contraction description
-- from Lemma 10.65.1 and Remark 10.18.5.
/-- Lemma 10.65.5 (2): if `R` is Noetherian and `N` is flat over `R`, then the associated primes
of `M ⊗[R] N` over `S` are exactly the fiberwise associated primes over those
`𝔭 ∈ Ass_R(M)`, viewed inside `Spec S` by the canonical maps from the fiber spectra. In Lean this
is expressed by equality with
`relativeAssassin R S N ∩ { q | q.asIdeal.under R ∈ associatedPrimesOfModule R M }`. -/
@[stacks 05C2]
theorem associatedPrimesOfModule_tensorProduct_eq_fiberAssociatedPrimes_of_isNoetherianRing
    [Module.Flat R N] [IsNoetherianRing R] :
    { q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) } =
      relativeAssassin R S N ∩
        { q : PrimeSpectrum S | q.asIdeal.under R ∈ associatedPrimesOfModule R M } := by
  ext q
  constructor
  · intro hq
    -- Expand the Noetherian equality from Lemma 10.65.3(2) to recover a prime-quotient witness.
    have hqUnion :
        q.asIdeal ∈ ⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
          associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) := by
      rw [← associatedPrimesOfModule.BaseChange.Flat.tensor_eq_iUnion_quotient
        (R := R) (S := S) (M := M) (N := N)]
      exact hq
    rcases Set.mem_iUnion.mp hqUnion with ⟨p, hqUnion⟩
    rcases Set.mem_iUnion.mp hqUnion with ⟨hp_assoc, hqQuot⟩
    have hp_assoc' : p ∈ associatedPrimesOfModule R M := hp_assoc
    have hp_prime : p.IsPrime := by
      rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp_assoc
      exact hp_assoc.1
    let pSpec : PrimeSpectrum R := ⟨p, hp_prime⟩
    -- Force the branch index to be the contraction `q ∩ R`.
    have hunder :
        q.asIdeal.under R = pSpec.asIdeal := by
      exact associatedPrimesOfModule.BaseChange.Flat.under_eq_of_mem_quotient
        (R := R) (S := S) (N := N) (p := pSpec.asIdeal) (q := q.asIdeal) hqQuot
    -- Rewrite the same witness back into the defining condition for `relativeAssassin`.
    have hqAfin : q ∈ relativeAssassinAfin R S N := by
      rw [mem_relativeAssassinAfin_iff, hunder]
      simpa [pSpec] using hqQuot
    have hqA : q ∈ relativeAssassin R S N := by
      rw [relativeAssassinA_eq_relativeAssassinAfin_of_flat (R := R) (S := S) (N := N)]
      exact hqAfin
    refine ⟨hqA, ?_⟩
    simpa [Set.mem_setOf_eq, pSpec] using (hunder.symm ▸ hp_assoc')
  · intro hq
    exact
      fiberAssociatedPrimes_subset_associatedPrimesOfModule_tensorProduct
        (R := R) (S := S) (M := M) (N := N) hq

end
