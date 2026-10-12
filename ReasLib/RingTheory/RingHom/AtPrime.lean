/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ring Homomorphism Properties at a Prime

This file owns the pointwise target-localization of an arbitrary property of
commutative ring homomorphisms.  It is the one-point counterpart of
`RingHom.Locally`: `AtPrime P f q` asks for one principal-open neighborhood of
`q` on which `P` holds.

@stack 00SY
-/

universe u v w

namespace RingHom

/-- A property `P` of commutative ring homomorphisms holds for `f` at a target
prime `q` if it holds after restricting the target to some principal-open
neighborhood of `q`.

Unlike `RingHom.Locally P f`, this definition records a neighborhood of one
specified point and does not choose a global open cover. -/
@[stacks 00SY "ring-homomorphism properties on a neighborhood of a prime"]
def AtPrime
    (P : ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B], (A →+* B) → Prop)
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ P ((algebraMap S (Localization.Away g)).comp f)

/-- The witness form of `RingHom.AtPrime`. -/
theorem atPrime_iff
    (P : ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B], (A →+* B) → Prop)
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) :
    AtPrime P f q ↔
      ∃ g : S, g ∉ q.asIdeal ∧ P ((algebraMap S (Localization.Away g)).comp f) :=
  Iff.rfl

namespace AtPrime

variable
  {P Q : ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B], (A →+* B) → Prop}
  {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  {f : R →+* S} {q : PrimeSpectrum S}

/-- A property holding on an explicit principal-open neighborhood holds at
every prime in that neighborhood. -/
theorem of_away {g : S} (hg : g ∉ q.asIdeal)
    (hf : P ((algebraMap S (Localization.Away g)).comp f)) :
    AtPrime P f q :=
  ⟨g, hg, hf⟩

/-- Pointwise target-localization is monotone in the ring-homomorphism
property. -/
theorem mono
    (hPQ : ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      {g : A →+* B}, P g → Q g)
    (hf : AtPrime P f q) : AtPrime Q f q := by
  obtain ⟨g, hg, hf⟩ := hf
  exact ⟨g, hg, hPQ hf⟩

end AtPrime

section Locally

variable
  {P : ∀ {A B : Type w} [CommRing A] [CommRing B], (A →+* B) → Prop}
  {R S : Type w} [CommRing R] [CommRing S]

/-- A property holds on a target standard-open cover exactly when it holds on
some principal-open neighborhood of every target prime. -/
theorem locally_iff_forall_atPrime (f : R →+* S) :
    Locally P f ↔ ∀ q : PrimeSpectrum S, AtPrime P f q := by
  rw [locally_iff_span_eq_top]
  constructor
  · intro hspan q
    have hnot : ¬ {g : S | P ((algebraMap S (Localization.Away g)).comp f)} ⊆ q.asIdeal := by
      intro hle
      exact q.2.ne_top (top_le_iff.mp (hspan ▸ Ideal.span_le.2 hle))
    obtain ⟨g, hgP, hgq⟩ := Set.not_subset.mp hnot
    exact ⟨g, hgq, hgP⟩
  · intro hf
    by_contra hspan
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hspan
    obtain ⟨g, hg, hPg⟩ := hf ⟨m, hm.isPrime⟩
    exact hg (hle (Ideal.subset_span hPg))

namespace Locally

/-- A target-locally valid property holds at each specified target prime. -/
theorem atPrime {f : R →+* S} (hf : Locally P f) (q : PrimeSpectrum S) :
    AtPrime P f q :=
  (locally_iff_forall_atPrime f).mp hf q

end Locally

/-- Pointwise principal-open witnesses at all target primes assemble into a
target standard-open cover. -/
theorem locally_of_forall_atPrime {f : R →+* S}
    (hf : ∀ q : PrimeSpectrum S, AtPrime P f q) : Locally P f :=
  (locally_iff_forall_atPrime f).mpr hf

end Locally

namespace PropertyIsLocal

variable
  {P : ∀ {A B : Type w} [CommRing A] [CommRing B], (A →+* B) → Prop}
  {R S : Type w} [CommRing R] [CommRing S]

/-- A target-local ring-homomorphism property holds globally exactly when it
holds on a principal-open neighborhood of every target prime. -/
theorem iff_forall_atPrime (hP : PropertyIsLocal P) (f : R →+* S) :
    P f ↔ ∀ q : PrimeSpectrum S, AtPrime P f q := by
  rw [← locally_iff_of_localizationSpanTarget hP.respectsIso hP.ofLocalizationSpanTarget,
    locally_iff_forall_atPrime]

end PropertyIsLocal

end RingHom
