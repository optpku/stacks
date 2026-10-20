module

public import ReasLib.RingTheory.AdicCompletion.PuncturedSpectrum
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.109.6 (0C2C)

@stack 0C2C
-/

open IsLocalRing

universe u v

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

-- Lemma 15.109.6, disconnectedness of punctured spectra under completion.
@[stacks 0C2C "Lemma 15.109.6"]
#check (IsHenselizationOf.Completion.puncturedSpectrum_not_preconnected_iff
    (A := A) (Ah := Ah) :
  ¬ PreconnectedSpace
      { p : PrimeSpectrum (AdicCompletion (maximalIdeal A) A) //
        p.asIdeal ≠ maximalIdeal (AdicCompletion (maximalIdeal A) A) } ↔
    ¬ PreconnectedSpace
      { p : PrimeSpectrum Ah // p.asIdeal ≠ maximalIdeal Ah })
