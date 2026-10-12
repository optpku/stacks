/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Local Characterizations of Nagata Rings

This module records the analytic-unramifiedness criterion for Noetherian local
Nagata rings.
-/

universe u v

namespace NagataRing

variable {R : Type u}

/-- Lemma 10.162.14, tag `0BI2`: for a Noetherian local ring, being Nagata is
equivalent to analytic unramifiedness after maximal localization of every
finite domain algebra, and to the corresponding finite local-domain test. -/
@[stacks 0BI2]
theorem local_tfae [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    List.TFAE
      [ NagataRing R,
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S],
          ∀ m : MaximalSpectrum S,
            IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal),
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S]
        [IsLocalRing S] [IsLocalHom (algebraMap R S)],
          IsAnalyticallyUnramified S ] := sorry

/-- The finite local-domain analytic-unramifiedness test implies that a
Noetherian local ring is Nagata. -/
theorem of_finiteLocalDomain_analyticallyUnramified
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h :
      ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S]
        [IsLocalRing S] [IsLocalHom (algebraMap R S)],
        IsAnalyticallyUnramified S) :
    NagataRing R := sorry

end NagataRing

namespace NagataRing

variable {R : Type u}

/-- A Nagata local ring has analytically unramified maximal localizations of
all finite domain algebras. -/
theorem analyticallyUnramified_atMaximal
    [CommRing R] [IsLocalRing R] [NagataRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S]
    (m : MaximalSpectrum S) :
    IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal) := sorry

end NagataRing
