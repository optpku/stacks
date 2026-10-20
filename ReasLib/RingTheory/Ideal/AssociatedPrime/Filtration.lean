/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Support
public import ReasLib.RingTheory.Ideal.AssociatedPrime.ExactSequence
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Quotient
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Support
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Prime Filtrations of Modules

A prime filtration is a finite relation series of submodules whose successive quotients are
linearly equivalent to prime quotients `R ⧸ p`.  The API below exposes its factors, support,
multiplicities, and associated-prime consequences without choosing an enumeration of the primes.
-/

universe u v w

open PrimeSpectrum RelSeries Submodule

namespace Module

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Lemma 10.62.1 (Tag 00L0): a prime filtration is a finite submodule series whose successive
quotients are prime quotients of the base ring. -/
@[stacks 00L0]
abbrev PrimeFiltration :=
  RelSeries {(N₁, N₂) : Submodule R M × Submodule R M |
    N₁.IsQuotientEquivQuotientPrime N₂}

end

/-- A module linearly equivalent to `R ⧸ p` has support `V(p)`. -/
theorem support_eq_zeroLocus_of_quotient_equiv
    {R : Type u} [CommRing R] {Q : Type w} [AddCommGroup Q] [Module R Q]
    {p : PrimeSpectrum R} (hQ : Nonempty (Q ≃ₗ[R] R ⧸ p.asIdeal)) :
    support R Q = zeroLocus p.asIdeal := sorry

namespace PrimeFiltration

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `i`-th successive quotient of a prime filtration. -/
abbrev successiveQuotient (s : PrimeFiltration R M) (i : Fin s.length) :=
  (s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)

/-- The prime points occurring as successive quotients of a prime filtration. -/
def primeFactors (s : PrimeFiltration R M) : Set (PrimeSpectrum R) :=
  {p | ∃ i : Fin s.length,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ p.asIdeal)}

/-- The number of stages of `s` whose quotient is linearly equivalent to `R ⧸ p`. -/
noncomputable def multiplicity (s : PrimeFiltration R M) (p : PrimeSpectrum R) : ℕ :=
  Set.ncard {i : Fin s.length |
    Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ p.asIdeal)}

/-- A module cannot be linearly equivalent to quotients by two distinct prime ideals. -/
theorem quotientPrime_unique {Q : Type w} [AddCommGroup Q] [Module R Q]
    {p q : PrimeSpectrum R}
    (hp : Nonempty (Q ≃ₗ[R] R ⧸ p.asIdeal))
    (hq : Nonempty (Q ≃ₗ[R] R ⧸ q.asIdeal)) :
    p = q := sorry

/-- The stage after an old index of `s.snoc N` is the corresponding stage of `s`. -/
@[simp]
theorem snoc_castSucc_succ
    (s : PrimeFiltration R M) {N : Submodule R M}
    (hrel : s.last.IsQuotientEquivQuotientPrime N) (i : Fin s.length) :
    s.snoc N hrel i.castSucc.succ = s i.succ :=
  (congrArg (s.snoc N hrel) (Fin.succ_castSucc i)).trans (RelSeries.snoc_castSucc _ _ _ _)

/-- The transport of a quotient `B ⧸ A` of submodules of `M` along equalities `A = A'` and
`B = B'`. -/
def _root_.Submodule.submoduleOfQuotEquivOfEq {A A' B B' : Submodule R M}
    (hA : A = A') (hB : B = B') :
    (B ⧸ A.submoduleOf B) ≃ₗ[R] (B' ⧸ A'.submoduleOf B') :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq B B' hB) (by subst hA hB; ext; simp)

/-- The transport `Submodule.submoduleOfQuotEquivOfEq` sends the class of `x` to the class of
`x`. -/
@[simp]
theorem _root_.Submodule.submoduleOfQuotEquivOfEq_mk {A A' B B' : Submodule R M}
    (hA : A = A') (hB : B = B') (x : B) :
    Submodule.submoduleOfQuotEquivOfEq hA hB (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (LinearEquiv.ofEq B B' hB x) := rfl

/-- Lemma 10.62.1 (Tag 00L0), filtration extension: earlier successive quotients are unchanged
when a final prime-quotient step is adjoined.  The equivalence is the identity transport along
the stage equalities of `RelSeries.snoc`. -/
def successiveQuotientSnocCastSuccEquiv
    (s : PrimeFiltration R M) {N : Submodule R M}
    (hrel : s.last.IsQuotientEquivQuotientPrime N) (i : Fin s.length) :
    successiveQuotient (s.snoc N hrel) i.castSucc ≃ₗ[R] s.successiveQuotient i :=
  Submodule.submoduleOfQuotEquivOfEq (RelSeries.snoc_castSucc s N hrel i.castSucc)
    (snoc_castSucc_succ s hrel i)

/-- The earlier-stage transport of `s.snoc N` sends the class of `x` to the class of `x`. -/
@[simp]
theorem successiveQuotientSnocCastSuccEquiv_mk
    (s : PrimeFiltration R M) {N : Submodule R M}
    (hrel : s.last.IsQuotientEquivQuotientPrime N) (i : Fin s.length)
    (x : s.snoc N hrel i.castSucc.succ) :
    successiveQuotientSnocCastSuccEquiv s hrel i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (LinearEquiv.ofEq _ _ (snoc_castSucc_succ s hrel i) x) := rfl

/-- The last successive quotient of `s.snoc N` is the newly adjoined quotient `N / s.last`,
via the identity transport along the stage equalities of `RelSeries.snoc`. -/
def successiveQuotientSnocLastEquiv
    (s : PrimeFiltration R M) {N : Submodule R M}
    (hrel : s.last.IsQuotientEquivQuotientPrime N) :
    successiveQuotient (s.snoc N hrel) (Fin.last s.length) ≃ₗ[R]
      (N ⧸ s.last.submoduleOf N) :=
  Submodule.submoduleOfQuotEquivOfEq (RelSeries.snoc_castSucc s N hrel (Fin.last _))
    (RelSeries.last_snoc' s N hrel)

/-- The last-stage transport of `s.snoc N` sends the class of `x` to the class of `x`. -/
@[simp]
theorem successiveQuotientSnocLastEquiv_mk
    (s : PrimeFiltration R M) {N : Submodule R M}
    (hrel : s.last.IsQuotientEquivQuotientPrime N)
    (x : s.snoc N hrel (Fin.last s.length).succ) :
    successiveQuotientSnocLastEquiv s hrel (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (LinearEquiv.ofEq _ _ (RelSeries.last_snoc' s N hrel) x) := rfl

/-- Prime factors already present in a filtration remain after adjoining one final step. -/
theorem primeFactors_subset_snoc
    (s : PrimeFiltration R M) {N : Submodule R M}
    (hrel : s.last.IsQuotientEquivQuotientPrime N) :
    s.primeFactors ⊆ primeFactors (s.snoc N hrel) := sorry

/-- The prime quotient in the final `snoc` step is a factor of the extended filtration. -/
theorem mem_primeFactors_snoc_last
    (s : PrimeFiltration R M) {N : Submodule R M} {p : PrimeSpectrum R}
    (hle : s.last ≤ N)
    (hp : Nonempty ((N ⧸ s.last.submoduleOf N) ≃ₗ[R] R ⧸ p.asIdeal)) :
    p ∈ primeFactors (s.snoc N ⟨hle, p, hp⟩) := sorry

/-- A prime occurs among the factors exactly when it has positive multiplicity. -/
@[simp]
theorem mem_primeFactors_iff_multiplicity_pos
    (s : PrimeFiltration R M) (p : PrimeSpectrum R) :
    p ∈ s.primeFactors ↔ 0 < s.multiplicity p := sorry

/-- A prime filtration starting at zero admits an enumeration of its factors whose zero loci
cover the support of its final stage. -/
theorem exists_factorPrimes (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) :
    ∃ p : Fin s.length → PrimeSpectrum R,
      (∀ i, Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal)) ∧
      support R s.last = ⋃ i, zeroLocus (p i).asIdeal := sorry

/-- Lemma 10.62.2: the support of a module is the union of the zero loci of the prime factors in
any prime filtration from `0` to the whole module. -/
@[stacks 00L4]
theorem support_eq_iUnion_zeroLocus
    (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    support R M = ⋃ p : s.primeFactors, zeroLocus p.1.asIdeal := sorry

/-- Every factor in a prime filtration from `0` to `M` belongs to `support R M`. -/
theorem primeFactors_subset_support
    (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    s.primeFactors ⊆ support R M := sorry

/-- Any enumeration realizing the successive quotients has range equal to the intrinsic factor
set. -/
theorem primeFactors_eq_range
    (s : PrimeFiltration R M) (p : Fin s.length → PrimeSpectrum R)
    (hp : ∀ i, Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal)) :
    s.primeFactors = Set.range p := sorry

/-- Lemma 10.62.5 (1): the minimal prime factors of a filtration are exactly the minimal points
of the module support. -/
@[stacks 00L7 "(1)"]
theorem minimal_primeFactor_iff_minimal_support
    (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    (p : PrimeSpectrum R) :
    Minimal (· ∈ s.primeFactors) p ↔ Minimal (· ∈ support R M) p := sorry

/-- Stacks `02CE`: for a prime filtration of a module over a Noetherian ring, its minimal prime
factors are exactly the minimal associated-prime points. -/
@[stacks 02CE "minimal filtration factors and associated-prime points"]
theorem minimal_primeFactor_iff_minimal_associatedPrimePoints [IsNoetherianRing R]
    (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    (p : PrimeSpectrum R) :
    Minimal (· ∈ s.primeFactors) p ↔
      Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M) p := sorry

/-- Stacks `02CE`: the minimal factors of a prime filtration are equivalently the minimal
exact-associated-prime points. -/
@[stacks 02CE "minimal filtration factors and exact-associated-prime points"]
theorem minimal_primeFactor_iff_minimal_exactAssociatedPrimePoints [IsNoetherianRing R]
    (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    (p : PrimeSpectrum R) :
    Minimal (· ∈ s.primeFactors) p ↔
      Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimesOfModule R M) p := sorry

/-- Lemma 10.62.5 (2): the multiplicity of a minimal factor equals the length of the localized
module at that prime. -/
@[stacks 00L7 "(2)"]
theorem multiplicity_eq_length
    (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    (p : PrimeSpectrum R) (hp : Minimal (· ∈ s.primeFactors) p) :
    (s.multiplicity p : ℕ∞) =
      Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) := sorry

/-- Exact associated primes of the final stage of a prime filtration come from its prime
factors. -/
theorem associatedPrimesOfLast_subset_primeFactors
    (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) :
    associatedPrimesOfModule R s.last ⊆
      PrimeSpectrum.asIdeal '' s.primeFactors := sorry

/-- Exact associated-prime points of `M` lie among the factors of any prime filtration from
`0` to `M`. -/
theorem associatedPrimePoints_subset_primeFactors
    (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimesOfModule R M ⊆
      s.primeFactors := sorry

/-- Lemma 10.63.4: exact associated primes of `M` occur in every chosen enumeration of the
factors of a prime filtration from `0` to `M`. -/
@[stacks 00LB]
theorem associatedPrimesOfModule_subset_range
    (s : PrimeFiltration R M) (p : Fin s.length → PrimeSpectrum R)
    (hp : ∀ i, Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    associatedPrimesOfModule R M ⊆ PrimeSpectrum.asIdeal '' Set.range p := sorry

/-- Over a Noetherian ring, mathlib's associated primes occur in every enumeration of the factors
of a prime filtration from `0` to `M`. -/
theorem associatedPrimes_subset_range [IsNoetherianRing R]
    (s : PrimeFiltration R M) (p : Fin s.length → PrimeSpectrum R)
    (hp : ∀ i, Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    associatedPrimes R M ⊆ PrimeSpectrum.asIdeal '' Set.range p := sorry

end

end PrimeFiltration

end Module
