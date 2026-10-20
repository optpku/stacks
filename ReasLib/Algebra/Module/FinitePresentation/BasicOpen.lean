module

public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation

@[expose] public section

universe u v w

open PrimeSpectrum
open scoped PrimeSpectrum

/-- Finite presentation of a module can be detected on a basic-open cover of the prime spectrum. -/
theorem Module.FinitePresentation.of_basicOpen_cover
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A) (hcover : (⨆ i, D(f i)) = ⊤)
    (h : ∀ i, Module.FinitePresentation (Localization.Away (f i))
      (LocalizedModule.Away (f i) M)) :
    Module.FinitePresentation A M := sorry
