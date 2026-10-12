/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Unramified.Locus
public import ReasLib.RingTheory.Kaehler.Fiber
public import ReasLib.RingTheory.Module.Support.Fiber
public import ReasLib.RingTheory.Unramified.Basic

/-!
# Kähler criteria for unramified points

The canonical local owner is `Algebra.IsUnramifiedAt`.  This leaf exposes the
Kähler-differential criteria at that owner and only then provides the
source-facing `UnramifiedAt` and `GUnramifiedAt` bridges. The underlying fiber
comparison is owned independently by `ReasLib.RingTheory.Kaehler.Fiber`.

@stack 00UV
-/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

namespace IsUnramifiedAt

/-- The canonical pointwise unramified predicate is equivalent to vanishing of
the localized module of Kähler differentials. -/
@[stacks 00UV "localized Kähler criterion for an unramified point"]
theorem iff_subsingleton_localizedKaehler (q : Ideal S) [q.IsPrime] :
    IsUnramifiedAt R q ↔
      Subsingleton (LocalizedModule.AtPrime q Ω[S⁄R]) := sorry

/-- For a finite Kähler module, vanishing of the residue-field Kähler fiber
is equivalent to the canonical pointwise unramified predicate. -/
@[stacks 00UV "Kähler fiber criterion for an unramified point"]
theorem iff_subsingleton_kaehlerFiber [Module.Finite S Ω[S⁄R]] (q : Ideal S) [q.IsPrime] :
    IsUnramifiedAt R q ↔ Subsingleton (q.Fiber Ω[S⁄R]) := sorry

/-!
The source clauses quantify a base point and a point above it. Keep that form
as the canonical owner; the `..._at` declarations below are convenience
specializations at `q.asIdeal.under R`. The spectrum-level `fiberPrime`
packages the lying-over equality without introducing a proof-indexed ideal
carrier.
-/

/-- Vanishing of the localized Kähler differential module of a residue-field
fiber at a point over `p` is equivalent to pointwise unramifiedness. -/
@[stacks 00UV "localized fiber Kähler criterion for an unramified point"]
theorem iff_subsingleton_fiberKaehlerLocalized
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    [Module.Finite S Ω[S⁄R]] :
    IsUnramifiedAt R q.asIdeal ↔
      Subsingleton (LocalizedModule.AtPrime
        (PrimeSpectrum.fiberPrime p q hq).asIdeal
        Ω[p.asIdeal.Fiber S⁄p.asIdeal.ResidueField]) := sorry

/-- Convenience specialization of the localized fiber criterion at the
contraction of a target point. -/
@[stacks 00UV "localized fiber Kähler criterion at a target point"]
theorem iff_subsingleton_fiberKaehlerLocalized_at
    (q : PrimeSpectrum S)
    [Module.Finite S Ω[S⁄R]] :
    IsUnramifiedAt R q.asIdeal ↔
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField]) := sorry

/- The same split is used for the residue-field fiber criterion. -/

/-- Vanishing of the Kähler differential residue fiber at a point over `p` is
equivalent to pointwise unramifiedness. -/
@[stacks 00UV "fiber Kähler criterion for an unramified point"]
theorem iff_subsingleton_fiberKaehlerFiber
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    [Module.Finite S Ω[S⁄R]] :
    IsUnramifiedAt R q.asIdeal ↔
      Subsingleton ((PrimeSpectrum.fiberPrime p q hq).asIdeal.Fiber
        Ω[p.asIdeal.Fiber S⁄p.asIdeal.ResidueField]) := sorry

/-- Convenience specialization of the residue-fiber criterion at a target
point. -/
@[stacks 00UV "fiber Kähler criterion at a target point"]
theorem iff_subsingleton_fiberKaehlerFiber_at
    (q : PrimeSpectrum S)
    [Module.Finite S Ω[S⁄R]] :
    IsUnramifiedAt R q.asIdeal ↔
      Subsingleton ((fiberPrimeAt R S q).asIdeal.Fiber
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField]) := sorry

end IsUnramifiedAt

namespace UnramifiedAt

/-- The source-facing basic-open predicate follows from localized Kähler
vanishing at a finite-type target prime. -/
@[stacks 00UV "source-facing localized Kähler criterion"]
theorem of_subsingleton_localizedKaehler [FiniteType R S] (q : PrimeSpectrum S)
    (hOmega : Subsingleton (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R])) :
    Algebra.UnramifiedAt R S q := sorry

/-- The source-facing basic-open predicate follows from Kähler-fiber
vanishing at a finite-type target prime. -/
@[stacks 00UV "source-facing Kähler fiber criterion"]
theorem of_subsingleton_kaehlerFiber [FiniteType R S] (q : PrimeSpectrum S)
    (hOmega : Subsingleton (q.asIdeal.Fiber Ω[S⁄R])) :
    Algebra.UnramifiedAt R S q := sorry

/-- The source-facing predicate follows from vanishing of the localized
Kähler module of the residue-field fiber. -/
@[stacks 00UV "source-facing localized fiber Kähler criterion"]
theorem of_subsingleton_fiberKaehlerLocalized [FiniteType R S] (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    Algebra.UnramifiedAt R S q := sorry

/-- The source-facing predicate follows from vanishing of the Kähler
differential residue fiber at the canonical fiber prime. -/
@[stacks 00UV "source-facing fiber Kähler criterion"]
theorem of_subsingleton_fiberKaehlerFiber [FiniteType R S] (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton ((fiberPrimeAt R S q).asIdeal.Fiber
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    Algebra.UnramifiedAt R S q := sorry

end UnramifiedAt

namespace GUnramifiedAt

/-- The source-facing G-unramified predicate follows from localized Kähler
vanishing at a finitely presented target prime. -/
@[stacks 00UV "source-facing localized Kähler criterion"]
theorem of_subsingleton_localizedKaehler [FinitePresentation R S] (q : PrimeSpectrum S)
    (hOmega : Subsingleton (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R])) :
    Algebra.GUnramifiedAt R S q := sorry

/-- The source-facing G-unramified predicate follows from Kähler-fiber
vanishing at a finitely presented target prime. -/
@[stacks 00UV "source-facing Kähler fiber criterion"]
theorem of_subsingleton_kaehlerFiber [FinitePresentation R S] (q : PrimeSpectrum S)
    (hOmega : Subsingleton (q.asIdeal.Fiber Ω[S⁄R])) :
    Algebra.GUnramifiedAt R S q := sorry

/-- The source-facing G-unramified predicate follows from vanishing of the
localized Kähler module of the residue-field fiber. -/
@[stacks 00UV "source-facing localized fiber Kähler criterion"]
theorem of_subsingleton_fiberKaehlerLocalized [FinitePresentation R S] (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    Algebra.GUnramifiedAt R S q := sorry

/-- The source-facing G-unramified predicate follows from vanishing of the
Kähler differential residue fiber at the canonical fiber prime. -/
@[stacks 00UV "source-facing fiber Kähler criterion"]
theorem of_subsingleton_fiberKaehlerFiber [FinitePresentation R S] (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton ((fiberPrimeAt R S q).asIdeal.Fiber
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    Algebra.GUnramifiedAt R S q := sorry

end GUnramifiedAt

end Algebra
