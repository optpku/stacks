module

public import ReasLib.RingTheory.Spectrum.Prime.Chevalley.DenseOpen
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.30.2

@stack 00FH

The constructible image of a finite-type map contains a dense open neighborhood inside the
closure of each point of the image.
-/

/- Lemma 10.30.2: for a finite-type ring map `f : R →+* S` and a constructible subset
`E ⊆ Spec(S)`, if `ξ ∈ Spec(R)` lies in the image of `E`, then that image contains an open dense
subset of `closure {ξ}`. -/
@[stacks 00FH]
#check @PrimeSpectrum.exists_open_dense_in_comap_image

@[stacks 00FH "spectrum comap owner"]
#check @PrimeSpectrum.comap
@[stacks 00FH "constructible image owner"]
#check @PrimeSpectrum.isConstructible_comap_image
