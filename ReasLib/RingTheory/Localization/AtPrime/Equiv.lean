module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spreading Prime-local Algebra Equivalences to Principal Opens

This leaf owns the finite-presentation descent statement that an equivalence
between two localizations at prime ideals extends, after shrinking both source
rings by elements outside those primes, to an equivalence of principal-open
localizations.  Prime ideals are used directly: the result has no topological
dependency on the bundled `PrimeSpectrum` interface.
-/

@[expose] public section

universe u v w

namespace Algebra.FinitePresentation.AtPrime

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']
variable [Algebra.FinitePresentation R S] [Algebra.FinitePresentation R S']

/-- Tag `00QS`: an `R`-algebra equivalence between the localizations of two
finitely presented `R`-algebras at prime ideals extends to an equivalence of
principal-open localizations after shrinking away from the two primes. -/
@[stacks 00QS "spreading prime-local algebra equivalences"]
theorem exists_awayAlgEquiv
    (q : Ideal S) [q.IsPrime] (q' : Ideal S') [q'.IsPrime]
    (h : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime q') :
    ∃ (g : S) (hg : g ∉ q), ∃ (g' : S') (hg' : g' ∉ q'),
      Nonempty (Localization.Away g ≃ₐ[R] Localization.Away g') := sorry

end Algebra.FinitePresentation.AtPrime
