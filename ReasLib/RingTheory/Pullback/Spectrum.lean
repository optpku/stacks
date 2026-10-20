module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Pullback.Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectra of Surjective Ring Pullbacks

For a surjective ring-pullback situation, this file packages the four contravariant spectrum maps
and the resulting pushout square of topological spaces.

@stack 0B7J
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

noncomputable section

namespace SurjectiveRingPullbackSituation

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

/-- The spectrum of the pullback ring in a surjective ring-pullback situation. -/
@[stacks 0B7J "spectrum of the pullback ring"]
abbrev specBprime : TopCat := TopCat.of (PrimeSpectrum S.Bprime)

/-- The spectrum map induced by the ring map `B ⟶ A`. -/
@[stacks 0B7J "spectrum map from the common target to B"]
abbrev specToB : TopCat.of (PrimeSpectrum A) ⟶ TopCat.of (PrimeSpectrum B) :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.toA, PrimeSpectrum.continuous_comap S.toA⟩

/-- The spectrum map induced by the ring map `A' ⟶ A`. -/
@[stacks 0B7J "spectrum map from the common target to A-prime"]
abbrev specToAprime : TopCat.of (PrimeSpectrum A) ⟶ TopCat.of (PrimeSpectrum A') :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.fromAprime,
    PrimeSpectrum.continuous_comap S.fromAprime⟩

/-- The spectrum map induced by the first pullback projection `B' ⟶ B`. -/
@[stacks 0B7J "spectrum map from B to the pullback"]
abbrev specBToBprime : TopCat.of (PrimeSpectrum B) ⟶ S.specBprime :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.bprimeToB,
    PrimeSpectrum.continuous_comap S.bprimeToB⟩

/-- The spectrum map induced by the second pullback projection `B' ⟶ A'`. -/
@[stacks 0B7J "spectrum map from A-prime to the pullback"]
abbrev specAprimeToBprime : TopCat.of (PrimeSpectrum A') ⟶ S.specBprime :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.bprimeToAprime,
    PrimeSpectrum.continuous_comap S.bprimeToAprime⟩

/-- The four spectrum maps of a surjective ring-pullback situation form a commutative square. -/
@[stacks 0B7J "spectrum square commutes"]
theorem specSquare_commutes :
    S.specToB ≫ S.specBToBprime = S.specToAprime ≫ S.specAprimeToBprime := sorry

/-- The spectrum of a surjective ring pullback is the pushout of the other three spectra. -/
@[stacks 0B7J "spectrum pushout"]
theorem spec_isPushout :
    IsPushout S.specToB S.specToAprime S.specBToBprime S.specAprimeToBprime := sorry

end SurjectiveRingPullbackSituation
