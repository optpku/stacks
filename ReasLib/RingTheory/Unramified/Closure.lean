/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import ReasLib.RingTheory.Unramified.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Closure properties of unramified algebras

Mathlib owns the finite-type predicate `Algebra.Unramified`.  This leaf adds
the closure and local-to-global API for ReasLib's finite-presentation
refinement `Algebra.GUnramified`.  The source-facing basic-open predicates
remain in `ReasLib.RingTheory.Unramified.Basic`.

@stack 00UV
-/

universe u v w x

open scoped TensorProduct

namespace Algebra

namespace Unramified

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.151.3 (7), tag `00UV`: a quotient of a commutative ring is
unramified over that ring. -/
@[stacks 00UV "quotients are unramified"]
theorem quotient (I : Ideal R) :
    Unramified R (R ⧸ I) := sorry

/-- Lemma 10.151.3 (19), tag `00UV`: unramifiedness descends from a finite
cover by principal localizations. -/
@[stacks 00UV "unramifiedness from a principal-open cover"]
theorem of_awayCover (s : Finset S)
    (hs : Ideal.span (↑s : Set S) = ⊤)
    (hlocal : ∀ f : s, Unramified R (Localization.Away f.1)) :
    Unramified R S := sorry

/-- Lemma 10.151.3 (21), tag `00UV`: unramifiedness is local for the
basic-open predicate `UnramifiedAt`. -/
@[stacks 00UV "unramifiedness from all basic-open neighborhoods"]
theorem of_at (hlocal : ∀ q : PrimeSpectrum S, UnramifiedAt R S q) :
    Unramified R S := sorry

/-- Unramifiedness is equivalent to unramifiedness on a principal-open
neighborhood of every target prime. -/
@[stacks 00UV "unramifiedness is local at target primes"]
theorem iff_forall_at :
    Unramified R S ↔ ∀ q : PrimeSpectrum S, UnramifiedAt R S q := sorry

/-- Pointwise Mathlib unramifiedness implies global unramifiedness for a
finite-type algebra. -/
@[stacks 00UV "unramifiedness from pointwise unramifiedness"]
theorem of_isUnramifiedAt [FiniteType R S]
    (hlocal : ∀ q : PrimeSpectrum S, IsUnramifiedAt R q.asIdeal) :
    Unramified R S := sorry

end Unramified

namespace GUnramified

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.151.3 (2), tag `00UV`: G-unramifiedness is stable under arbitrary
base change. -/
@[stacks 00UV "G-unramified base change"]
theorem baseChange {R' : Type w} [CommRing R'] [Algebra R R'] [GUnramified R S] :
    GUnramified R' (R' ⊗[R] S) := sorry

/-- Lemma 10.151.3 (4), tag `00UV`: G-unramifiedness is stable under
composition of algebra maps. -/
@[stacks 00UV "composition of G-unramified algebras"]
theorem comp {T : Type x} [CommRing T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [GUnramified R S] [GUnramified S T] :
    GUnramified R T := sorry

/-- Lemma 10.151.3 (6), tag `00UV`: a principal localization is
G-unramified over its base ring. -/
@[stacks 00UV "principal localizations are G-unramified"]
theorem of_localizationAway (f : R) :
    GUnramified R (Localization.Away f) := sorry

/-- Lemma 10.151.3 (8), tag `00UV`: a quotient by a finitely generated ideal
is G-unramified. -/
@[stacks 00UV "finitely generated quotients are G-unramified"]
theorem quotient_of_fg (I : Ideal R) (hI : I.FG) :
    GUnramified R (R ⧸ I) := sorry

/-- Lemma 10.151.3 (10), tag `00UV`: every etale algebra is G-unramified. -/
@[stacks 00UV "etale algebras are G-unramified"]
theorem of_etale [Etale R S] :
    GUnramified R S := sorry

/-- Lemma 10.151.3 (20), tag `00UV`: G-unramifiedness descends from a finite
cover by principal localizations. -/
@[stacks 00UV "G-unramifiedness from a principal-open cover"]
theorem of_awayCover (s : Finset S)
    (hs : Ideal.span (↑s : Set S) = ⊤)
    (hlocal : ∀ f : s, GUnramified R (Localization.Away f.1)) :
    GUnramified R S := sorry

/-- Lemma 10.151.3 (22), tag `00UV`: G-unramifiedness is local for the
basic-open predicate `GUnramifiedAt`. -/
@[stacks 00UV "G-unramifiedness from all basic-open neighborhoods"]
theorem of_at (hlocal : ∀ q : PrimeSpectrum S, GUnramifiedAt R S q) :
    GUnramified R S := sorry

/-- G-unramifiedness is equivalent to G-unramifiedness on a principal-open
neighborhood of every target prime. -/
@[stacks 00UV "G-unramifiedness is local at target primes"]
theorem iff_forall_at :
    GUnramified R S ↔ ∀ q : PrimeSpectrum S, GUnramifiedAt R S q := sorry

/-- Pointwise Mathlib unramifiedness implies global G-unramifiedness for a
finitely presented algebra. -/
@[stacks 00UV "G-unramifiedness from pointwise unramifiedness"]
theorem of_isUnramifiedAt [FinitePresentation R S]
    (hlocal : ∀ q : PrimeSpectrum S, IsUnramifiedAt R q.asIdeal) :
    GUnramified R S := sorry

end GUnramified

end Algebra
