module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
public import ReasLib.RingTheory.Henselian.Henselization.Completion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Punctured spectra of henselizations and completions

Disconnectedness of the punctured spectrum is unchanged when passing between a henselization of a
Noetherian local ring and its maximal-ideal completion.

@stack 0C2C
-/

@[expose] public section

open IsLocalRing

universe u v

namespace IsHenselizationOf.Completion

/-- Lemma 15.109.6: the punctured spectrum of the completion of a Noetherian local ring is
disconnected exactly when the punctured spectrum of a chosen henselization is disconnected. -/
@[stacks 0C2C "Lemma 15.109.6"]
theorem puncturedSpectrum_not_preconnected_iff
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] :
    ¬ PreconnectedSpace
        { p : PrimeSpectrum (AdicCompletion (maximalIdeal A) A) //
          p.asIdeal ≠ maximalIdeal (AdicCompletion (maximalIdeal A) A) } ↔
      ¬ PreconnectedSpace
        { p : PrimeSpectrum Ah // p.asIdeal ≠ maximalIdeal Ah } := sorry
-- Proof strategy: compare idempotent decompositions of the two punctured spectra through the
-- henselization-to-completion map; faithful flatness and the local comparison identify their
-- clopen decompositions, hence preconnectedness.

end IsHenselizationOf.Completion
