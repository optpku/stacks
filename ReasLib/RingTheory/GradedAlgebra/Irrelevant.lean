module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import ReasLib.RingTheory.GradedAlgebra.DegreeZero
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The irrelevant ideal of a nonnegatively graded algebra

This file owns the reusable algebra around the irrelevant ideal.  Minimal-prime
homogeneity is stated independently of any base field.  Maximality and the
closed point are then exposed first from a field structure on the degree-zero
piece and second through the source-facing degree-zero equivalence.
-/

open scoped HomogeneousIdeal

universe u v w

namespace Ideal.IsHomogeneous

variable {S : Type v} {σ : Type w}
variable [CommRing S] [SetLike σ S] [AddSubmonoidClass σ S]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- Lemma 10.57.8 (2), Stacks 00JU: a minimal prime over a homogeneous ideal is
homogeneous. -/
@[stacks 00JU "minimal primes over a homogeneous ideal"]
theorem minimalPrime {I p : Ideal S} (hI : I.IsHomogeneous 𝒜)
    (hp : p ∈ I.minimalPrimes) :
    p.IsHomogeneous 𝒜 := sorry

end Ideal.IsHomogeneous

namespace Ideal

variable {S : Type v} {σ : Type w}
variable [CommRing S] [SetLike σ S] [AddSubmonoidClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Lemma 10.57.8 (1), Stacks 00JU: every minimal prime of a nonnegatively
graded commutative ring is homogeneous. -/
@[stacks 00JU "minimal primes of a graded ring"]
theorem isHomogeneous_of_mem_minimalPrimes {p : Ideal S}
    (hp : p ∈ minimalPrimes S) :
    p.IsHomogeneous 𝒜 := sorry

end Ideal

namespace HomogeneousIdeal

section PositiveGenerators

variable {S : Type v} {σ : Type w}
variable [CommSemiring S] [SetLike σ S] [AddSubmonoidClass σ S]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜] {s : Set S}

/-- Positive-degree homogeneous elements span an ideal contained in the
irrelevant ideal. -/
@[stacks 07Z4 "positive homogeneous generators span inside the irrelevant ideal"]
theorem span_le_irrelevant
    (hs : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Ideal.span s ≤ 𝒜₊.toIdeal := sorry

/-- Positive-degree homogeneous elements generate the graded semiring over
its degree-zero part exactly when their ideal contains the irrelevant ideal. -/
@[stacks 07Z4 "algebra generators and containment of the irrelevant ideal"]
theorem adjoin_eq_top_iff_irrelevant_le_span
    (hs : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Algebra.adjoin (𝒜 0) s = ⊤ ↔ 𝒜₊.toIdeal ≤ Ideal.span s := sorry

/-- Positive-degree homogeneous elements generate the graded semiring over
its degree-zero part exactly when they generate the irrelevant ideal. -/
@[stacks 07Z4 "positive homogeneous generators of a graded semiring"]
theorem adjoin_eq_top_iff_span_eq_irrelevant
    (hs : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Algebra.adjoin (𝒜 0) s = ⊤ ↔ Ideal.span s = 𝒜₊.toIdeal := sorry

end PositiveGenerators

section IrrelevantBot

variable {S : Type v} {σ : Type w}
variable [CommSemiring S] [SetLike σ S] [AddSubmonoidClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A positive-degree homogeneous element is zero when the irrelevant ideal is zero. -/
@[stacks 00K1 "positive graded piece vanishes with zero irrelevant ideal"]
theorem eq_zero_of_mem_of_irrelevant_eq_bot
    {d : ℕ} (hd : 0 < d) {x : S} (hx : x ∈ 𝒜 d)
    (hbot : 𝒜₊.toIdeal = ⊥) :
    x = 0 := sorry

end IrrelevantBot

section FieldDegreeZero

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]

/-- The irrelevant ideal is maximal when the degree-zero piece is a field. -/
@[stacks 00P6 "(1), irrelevant ideal maximality"]
theorem irrelevant_isMaximal (hzero : IsField (𝒜 0)) :
    𝒜₊.toIdeal.IsMaximal := sorry

end FieldDegreeZero

section DegreeZeroEquiv

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]

/-- The source-facing maximality criterion obtained from an identification of
the degree-zero piece with the base field. -/
@[stacks 00P6 "(1), irrelevant ideal maximality"]
theorem irrelevant_isMaximal_of_degreeZeroEquiv
    (zeroEquiv : k ≃ₐ[k] 𝒜 0) :
    𝒜₊.toIdeal.IsMaximal := sorry

/-- The closed point of `Spec(S)` defined by the irrelevant ideal.  Its ideal
is explicit; only the proof of maximality is deferred. -/
@[stacks 00P6 "irrelevant closed point"]
def irrelevantMaximalSpectrum (zeroEquiv : k ≃ₐ[k] 𝒜 0) :
    MaximalSpectrum S :=
  ⟨𝒜₊.toIdeal, irrelevant_isMaximal_of_degreeZeroEquiv 𝒜 zeroEquiv⟩

end DegreeZeroEquiv

end HomogeneousIdeal

namespace Ideal.IsHomogeneous

section FieldDegreeZero

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {𝒜 : ℕ → Submodule R S} [GradedAlgebra 𝒜]

/-- Every proper homogeneous ideal is contained in the irrelevant ideal when
the degree-zero piece is a field. -/
@[stacks 00P6 "homogeneous ideals lie in the irrelevant ideal"]
theorem le_irrelevant {I : Ideal S} (hzero : IsField (𝒜 0))
    (hI : I.IsHomogeneous 𝒜) (hne : I ≠ ⊤) :
    I ≤ 𝒜₊.toIdeal := sorry

end FieldDegreeZero

section DegreeZeroEquiv

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable {𝒜 : ℕ → Submodule k S} [GradedAlgebra 𝒜]

/-- A degree-zero equivalence gives the source-facing containment of every
proper homogeneous ideal in the irrelevant ideal. -/
@[stacks 00P6 "homogeneous ideals lie in the irrelevant ideal"]
theorem le_irrelevant_of_degreeZeroEquiv {I : Ideal S}
    (hI : I.IsHomogeneous 𝒜) (zeroEquiv : k ≃ₐ[k] 𝒜 0)
    (hne : I ≠ ⊤) :
    I ≤ 𝒜₊.toIdeal := sorry

end DegreeZeroEquiv

end Ideal.IsHomogeneous

namespace HomogeneousIdeal

section FieldDegreeZero

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]

/-- Every minimal prime lies below the irrelevant ideal when the degree-zero
piece is a field. -/
@[stacks 00P6 "(2), minimal primes lie below the irrelevant ideal"]
theorem minimalPrime_le_irrelevant (hzero : IsField (𝒜 0))
    (p : minimalPrimes S) :
    p.1 ≤ 𝒜₊.toIdeal := sorry

end FieldDegreeZero

section DegreeZeroEquiv

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]

/-- Every minimal prime lies below the irrelevant ideal after identifying the
degree-zero piece with the base field. -/
@[stacks 00P6 "(2), minimal primes lie below the irrelevant ideal"]
theorem minimalPrime_le_irrelevant_of_degreeZeroEquiv
    (zeroEquiv : k ≃ₐ[k] 𝒜 0) (p : minimalPrimes S) :
    p.1 ≤ 𝒜₊.toIdeal := sorry

end DegreeZeroEquiv

end HomogeneousIdeal
