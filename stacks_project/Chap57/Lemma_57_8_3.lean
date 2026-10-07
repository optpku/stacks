module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.Composition

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 57.8.3: under quasi-compactness and quasi-separatedness, flatness of the middle
structural morphism, and Tor-independence of the outer schemes, composition of quasicoherent
Fourier--Mukai transforms is naturally isomorphic to the transform associated to the derived
convolution kernel. -/
@[stacks 0FYS]
#check (AlgebraicGeometry.Scheme.FourierMukai.compositionIsoExists :
  ∀ {S X Y Z T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact h] [QuasiSeparated h] [Flat g],
    Scheme.TorIndependentOver (Over.mk f) (Over.mk h) →
    (p12 : T ⟶ Limits.pullback f g) →
    (p23 : T ⟶ Limits.pullback g h) →
    (p13 : T ⟶ Limits.pullback f h) →
    IsPullback p12 p23 (Limits.pullback.snd f g) (Limits.pullback.fst g h) →
    p13 ≫ Limits.pullback.fst f h = p12 ≫ Limits.pullback.fst f g →
    p13 ≫ Limits.pullback.snd f h = p23 ≫ Limits.pullback.snd g h →
    (K : Scheme.DerivedQCoh (Limits.pullback f g)) →
    (K' : Scheme.DerivedQCoh (Limits.pullback g h)) →
    Nonempty ((AlgebraicGeometry.Scheme.FourierMukai.quasicoherent f g K ⋙
        AlgebraicGeometry.Scheme.FourierMukai.quasicoherent g h K') ≅
      AlgebraicGeometry.Scheme.FourierMukai.quasicoherent f h
        (AlgebraicGeometry.Scheme.FourierMukai.quasicoherentConvolutionKernel
          f g h p12 p23 p13 _ _ _ K K')))
