/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Localization
public import ReasLib.RingTheory.RingHom.AtPrime

@[expose] public section

/-!
# Finite Presentation and Flatness at a Prime

This leaf owns pointwise principal-open finite-presentation and local-ring
flatness predicates for arbitrary commutative ring homomorphisms.

@stack 00QT
@stack 07FH
@stack 00SC
@stack 00SY
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The local source ring at the contraction of a target prime. -/
@[stacks 07FH "source local ring at a target prime"]
abbrev sourceLocalRingAt (f : R →+* S) (q : PrimeSpectrum S) : Type u :=
  Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal

/-- The map between the source and target local rings induced by a ring
homomorphism at a target prime. -/
@[stacks 07FH "map on local rings at a target prime"]
noncomputable def localRingHomAt (f : R →+* S) (q : PrimeSpectrum S) :
    f.sourceLocalRingAt q →+* Localization.AtPrime q.asIdeal :=
  Localization.localRingHom (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl

namespace localRingHomAt

/-- The canonical map between the source and target localizations is local. -/
@[stacks 07FH "localized ring map is local"]
instance instIsLocalHom (f : R →+* S) (q : PrimeSpectrum S) :
    IsLocalHom (f.localRingHomAt q) :=
  Localization.isLocalHom_localRingHom
    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl

end localRingHomAt

namespace LocalTarget

variable {A : Type u} {B : Type v}
variable [CommSemiring A] [CommSemiring B] [IsLocalRing B]

/-- The canonical map from the localization of `A` at the contraction of the
maximal ideal of `B` to the local target `B`.  It is the composite of the
prime-localization map induced by `f` and the canonical identification of
`B` with the localization at its maximal-ideal complement. -/
@[stacks 00QT "localization at a contracted closed point"]
noncomputable def mapAtClosedPoint (f : A →+* B) :
    Localization.AtPrime (Ideal.comap f (IsLocalRing.maximalIdeal B)) →+* B :=
  -- Local instance justification (defeq pin): install the canonical localization
  -- structure so the explicit comparison map elaborates with its intended type.
  letI : IsLocalization (IsLocalRing.maximalIdeal B).primeCompl B :=
    IsLocalRing.isLocalization_primeCompl_maximalIdeal
  (IsLocalization.algEquiv
      (IsLocalRing.maximalIdeal B).primeCompl
      (Localization.AtPrime (IsLocalRing.maximalIdeal B)) B).toRingHom.comp
    (Localization.localRingHom
      (Ideal.comap f (IsLocalRing.maximalIdeal B))
      (IsLocalRing.maximalIdeal B) f rfl)

/-- The contracted-point localization map sends the canonical image of a base
element to its value under the original ring homomorphism. -/
@[simp, stacks 00QT "localization at a contracted closed point"]
theorem mapAtClosedPoint_to_map (f : A →+* B) (x : A) :
    mapAtClosedPoint f
        (algebraMap A
          (Localization.AtPrime (Ideal.comap f (IsLocalRing.maximalIdeal B))) x) =
      f x := sorry

/-- Injectivity of a ring homomorphism is preserved by the canonical map from
the contracted-point localization into a local target. -/
@[stacks 00QT "injectivity after localization at a contracted closed point"]
theorem mapAtClosedPoint_injective (f : A →+* B)
    (hf : Function.Injective f) :
    Function.Injective (mapAtClosedPoint f) := sorry

end LocalTarget

/-- The extension of the kernel of a ring homomorphism to its local source
ring at a target prime. -/
@[stacks 00SC "localized kernel at a target prime"]
noncomputable def localKernelIdealAt (f : R →+* S) (q : PrimeSpectrum S) :
    Ideal (f.sourceLocalRingAt q) :=
  Ideal.map (algebraMap R (f.sourceLocalRingAt q)) (RingHom.ker f)

namespace localKernelIdealAt

/-- The localized kernel of a ring homomorphism lies in the maximal ideal of its local source
ring. -/
@[stacks 00SC "localized kernel lies in the source maximal ideal"]
theorem le_maximalIdeal (f : R →+* S) (q : PrimeSpectrum S) :
    f.localKernelIdealAt q ≤ IsLocalRing.maximalIdeal (f.sourceLocalRingAt q) := sorry

/-- The localized kernel of a ring homomorphism lies in the Jacobson radical of its local source
ring. -/
@[stacks 00SC "localized kernel lies in the source Jacobson radical"]
theorem le_jacobson (f : R →+* S) (q : PrimeSpectrum S) :
    f.localKernelIdealAt q ≤ Ring.jacobson (f.sourceLocalRingAt q) := sorry

/-- A principal kernel remains principal after passing to the source local ring. -/
@[stacks 00SC "localized principal kernel"]
theorem eq_span_singleton_of_ker_eq_span
    (f : R →+* S) (q : PrimeSpectrum S) (x : R)
    (hker : RingHom.ker f = Ideal.span ({x} : Set R)) :
    f.localKernelIdealAt q =
      Ideal.span ({algebraMap R (f.sourceLocalRingAt q) x} :
        Set (f.sourceLocalRingAt q)) := by
  rw [RingHom.localKernelIdealAt, hker, Ideal.map_span]
  simp only [Set.image_singleton]

end localKernelIdealAt

/-- The quotient of the local source ring by the localized kernel of a ring
homomorphism at a target prime. -/
@[stacks 00SY "local source quotient by the localized kernel"]
abbrev localQuotientAt (f : R →+* S) (q : PrimeSpectrum S) : Type u :=
  f.sourceLocalRingAt q ⧸ f.localKernelIdealAt q

/-- A ring homomorphism is of finite presentation at a target prime when it is
of finite presentation on a principal-open neighbourhood of that prime. -/
@[stacks 00SY "finite presentation at a prime"]
def FinitePresentationAt (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  AtPrime (fun g ↦ g.FinitePresentation) f q

namespace FinitePresentationAt

/-- Finite presentation at a target prime is the existence of a
finite-presentation restriction to a principal-open neighborhood. -/
theorem iff_exists_away (f : R →+* S) (q : PrimeSpectrum S) :
    f.FinitePresentationAt q ↔
      ∃ g : S, g ∉ q.asIdeal ∧
        ((algebraMap S (Localization.Away g)).comp f).FinitePresentation := sorry

end FinitePresentationAt

/-- A ring homomorphism is flat at a target prime when the induced map between
the local rings at the contracted and target primes is flat. -/
@[stacks 00SY "flatness at a prime"]
def FlatAt (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  (f.localRingHomAt q).Flat

namespace FinitePresentation

/-- A finitely presented ring homomorphism is of finite presentation at every
target prime. -/
@[stacks 00SY "finite presentation implies finite presentation at a prime"]
theorem atPrime {f : R →+* S} (hf : f.FinitePresentation) (q : PrimeSpectrum S) :
    f.FinitePresentationAt q := sorry

/-- Finite presentation is equivalent to finite presentation on a
principal-open neighborhood of every target prime. -/
theorem iff_forall_atPrime (f : R →+* S) :
    f.FinitePresentation ↔ ∀ q : PrimeSpectrum S, f.FinitePresentationAt q := sorry

end FinitePresentation

namespace Flat

/-- A flat ring homomorphism is flat at every target prime. -/
@[stacks 00SY "flatness implies flatness at a prime"]
theorem atPrime {f : R →+* S} (hf : f.Flat) (q : PrimeSpectrum S) :
    f.FlatAt q := sorry

end Flat

end RingHom
