module

public import ReasLib.RingTheory.Spectrum.Prime.Jacobson.ConstructibleImage
import StacksCheckRecall

/-!
# Constructible images and closed-point traces

Lemma 10.35.22 combines the finite-type form of Chevalley's theorem over a Noetherian ring with
the canonical closed-point trace comparison for Jacobson spectra.  The two atomic owners are
recalled separately so downstream code can use either conclusion without unpacking a conjunction.

@stack 00GE
-/

@[expose] public section

@[stacks 00GE "constructible image"]
#check @RingHom.FiniteType.isConstructible_comap_image

@[stacks 00GE "closed-point trace commutes with the image"]
#check @PrimeSpectrum.closedPointsTrace_comap_image
