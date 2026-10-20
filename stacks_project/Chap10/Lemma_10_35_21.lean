module

public import ReasLib.RingTheory.Spectrum.Prime.Jacobson.ConstructibleImage
import StacksCheckRecall

/-!
# Closed points in constructible images

Lemma 10.35.21 is owned by the closed-point image API for finite-type maps between Jacobson
spectra.  The chapter records both source clauses and the reusable closed-point trace bridge.

@stack 00GD
-/

@[expose] public section

@[stacks 00GD "(1), closed points of a constructible image"]
#check @PrimeSpectrum.closedPoints_comap_image

@[stacks 00GD "closed-point trace of a constructible image"]
#check @PrimeSpectrum.closedPointsTrace_comap_image

@[stacks 00GD "(2), dense closed-point trace"]
#check @PrimeSpectrum.mem_comap_image_iff_dense_closedPoints
