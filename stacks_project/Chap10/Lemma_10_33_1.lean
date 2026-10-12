/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Localization.ClosedImage
import StacksCheckRecall

/-!
# Closed images on prime spectra

@stack 02JH
-/

@[expose] public section

/- Lemma 10.33.1: if the image of `Spec(S⁻¹R) → Spec(R)` is closed, then `S⁻¹R` is isomorphic to
the quotient `R / I` for some ideal `I ⊆ R`. -/
@[stacks 02JH "quotient presentation"]
#check @Localization.exists_ideal_ringEquiv_quotient_of_isClosed_range_comap

/- Closed image of `Spec(S⁻¹R) → Spec(R)` forces the localization map `R → S⁻¹R` to be
surjective. -/
@[stacks 02JH "surjective localization map"]
#check @Localization.algebraMap_surjective_of_isClosed_range_comap
