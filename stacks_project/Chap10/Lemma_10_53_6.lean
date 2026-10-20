module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCheckRecall

/-!
@stack 00JB
-/

@[expose] public section

universe u

section

variable (R : Type u) [CommRing R]

/- Lemma 10.53.6 (1): a commutative ring is Artinian exactly when it
has finite length as a module over itself. -/
@[stacks 00JB "(1)"]
#check (isArtinianRing_iff_isFiniteLength R :
  IsArtinianRing R ↔ IsFiniteLength R R)

section

variable [IsArtinianRing R]

/- Lemma 10.53.6 (2): an Artinian commutative ring is Noetherian. -/
@[stacks 00JB "(2)"]
#check (inferInstance : IsNoetherianRing R)

/- Lemma 10.53.6 (3): every prime ideal of an Artinian commutative
ring is maximal. -/
@[stacks 00JB "(3)"]
#check @IsArtinianRing.isPrime_iff_isMaximal

/- Lemma 10.53.6 (4): an Artinian commutative ring has finite maximal
spectrum. -/
@[stacks 00JB "(4)"]
#check (inferInstance : Finite (MaximalSpectrum R))

/- Lemma 10.53.6 (5): an Artinian commutative ring is the finite
product of its localizations at maximal ideals. -/
@[stacks 00JB "(5)"]
#check ((MaximalSpectrum.toPiLocalizationEquiv R).toRingEquiv :
  R ≃+* MaximalSpectrum.PiLocalization R)

end

end
