module

public import ReasLib.RingTheory.RingHom.Local.WLocal
import StacksCheckRecall

/-!
# Lemma 61.6.4

A ring map that identifies local rings, with w-local spectra, a w-local
spectrum map, and a bijection on connected components, is an isomorphism.
-/

@[expose] public section

universe u

open PrimeSpectrum

/- Lemma 61.6.4: if `f : A →+* B` identifies local rings, `PrimeSpectrum A` and
`PrimeSpectrum B` are w-local, `comap f` is w-local, and
`(continuous_comap f).connectedComponentsMap` is bijective, then `f` is
bijective. -/
@[stacks 097E] #check
  (RingHom.IsIsoOnLocalRings.bijective_of_bijective_connectedComponents :
    ∀ {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    [WLocalSpace (PrimeSpectrum A)] [WLocalSpace (PrimeSpectrum B)]
    [IsWLocalMap (comap f)] (hf : f.IsIsoOnLocalRings)
    (h_connectedComponents :
      Function.Bijective (continuous_comap f).connectedComponentsMap),
    Function.Bijective f)
