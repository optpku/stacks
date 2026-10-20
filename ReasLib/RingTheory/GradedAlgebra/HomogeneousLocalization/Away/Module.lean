module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero parts away from one homogeneous element

This leaf provides the powers-of-one-element presentation of the generic degree-zero homogeneous
localized module construction.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace HomogeneousLocalization.Away.Module

variable {ι : Type u} [AddCommMonoid ι] [DecidableEq ι]
variable {S : Type v} [CommRing S]
variable {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
variable {M : Type z} [AddCommMonoid M] [Module S M]
variable {τ : Type*} [SetLike τ M] [AddSubmonoidClass τ M]
variable (𝒜 : ι → σ) (ℳ : ι → τ)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

/-- The standard fraction `m / f^n` in the ordinary localization away from `f`. -/
@[stacks 07Z2 "homogeneous localized module standard fraction"]
noncomputable abbrev powMk {d : ι} (f : 𝒜 d) (n : ℕ) (m : M) :
    LocalizedModule.Away (f : S) M :=
  LocalizedModule.mk m ⟨(f : S) ^ n, pow_mem (Submonoid.mem_powers (f : S)) n⟩

/-- The well-typed standard fraction whose numerator has the degree required for a degree-zero
away fraction.  The raw `powMk` remains available for calculations on arbitrary numerators. -/
@[stacks 07Z2 "homogeneous standard fraction with typed numerator"]
noncomputable abbrev powMkHomogeneous {d : ι} (f : 𝒜 d) (n : ℕ) (m : ℳ (n • d)) :
    LocalizedModule.Away (f : S) M :=
  powMk 𝒜 f n (m : M)

/-- The degree-zero part after localization away from the homogeneous element `f`. -/
@[stacks 07Z2 "degree-zero homogeneous localization of a module"]
noncomputable abbrev degreeZeroPart {d : ι} (f : 𝒜 d) :
    Submodule (HomogeneousLocalization.Away 𝒜 (f : S)) (LocalizedModule.Away (f : S) M) :=
  HomogeneousLocalization.Module.degreeZeroPart 𝒜 ℳ (Submonoid.powers (f : S))

/-- Membership in the degree-zero part away from `f` is equivalent to a standard representative
whose numerator has degree `n • d`. -/
@[stacks 07Z2 "degree-zero homogeneous localization membership"]
theorem mem_degreeZeroPart_iff {d : ι} (f : 𝒜 d) {z : LocalizedModule.Away (f : S) M} :
    z ∈ degreeZeroPart 𝒜 ℳ f ↔
      ∃ n, ∃ m : ℳ (n • d), z = powMkHomogeneous 𝒜 ℳ f n m := by
  change
    (∃ i, ∃ m : ℳ i, ∃ s : 𝒜 i, ∃ hs : (s : S) ∈ Submonoid.powers (f : S),
      z = LocalizedModule.mk (m : M) ⟨(s : S), hs⟩) ↔ _
  constructor
  · rintro ⟨i, m, s, hs, rfl⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : S) (f : S)).mp hs
    by_cases hfn : (f : S) ^ n = 0
    · have hzero : (0 : S) ∈ Submonoid.powers (f : S) := by
        rw [← hfn]
        exact ⟨n, rfl⟩
      -- Local instance justification (proof-local temporary data): the zero-denominator branch uses subsingleton localization only to prove representative equality.
      letI := LocalizedModule.subsingleton (M := M) hzero
      exact ⟨n, 0, Subsingleton.elim _ _⟩
    · have hdegree : i = n • d :=
        DirectSum.degree_eq_of_mem_mem 𝒜 s.2
          (hn ▸ SetLike.pow_mem_graded n f.2) (hn ▸ hfn)
      subst i
      refine ⟨n, m, ?_⟩
      congr 1
      exact Subtype.ext hn.symm
  · rintro ⟨n, m, rfl⟩
    refine ⟨n • d, m, ⟨(f : S) ^ n, SetLike.pow_mem_graded n f.2⟩,
      ⟨n, rfl⟩, ?_⟩
    rfl

/-- A standard fraction with numerator in degree `n • d` belongs to the degree-zero part away
from `f`. -/
@[stacks 07Z2 "degree-zero homogeneous localization standard fraction membership"]
theorem mk_mem_degreeZeroPart {d : ι} (f : 𝒜 d) {n : ℕ} {m : M}
    (hm : m ∈ ℳ (n • d)) :
    powMk 𝒜 f n m ∈ degreeZeroPart 𝒜 ℳ f := sorry

/-- A typed homogeneous numerator gives a standard degree-zero away fraction. -/
@[stacks 07Z2 "typed homogeneous fraction membership"]
theorem powMkHomogeneous_mem_degreeZeroPart {d : ι} (f : 𝒜 d) {n : ℕ}
    (m : ℳ (n • d)) :
    powMkHomogeneous 𝒜 ℳ f n m ∈ degreeZeroPart 𝒜 ℳ f := sorry

end HomogeneousLocalization.Away.Module
