module

public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import StacksCheckRecall

/-!
# Constructible images under a principal-open localization

@stack 00F9

Lemma 10.29.5 specializes Chevalley's theorem using finite presentation of a
principal localization.
-/

@[expose] public section

@[stacks 00F9 "constructible image owner"]
#check @PrimeSpectrum.isConstructible_comap_image

@[stacks 00F9 "finite-presentation map criterion"]
#check @RingHom.finitePresentation_algebraMap

@[stacks 00F9 "principal localization is finitely presented"]
#check @IsLocalization.Away.finitePresentation
