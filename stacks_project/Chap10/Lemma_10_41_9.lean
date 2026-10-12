/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.PrimeSpectrum.Subalgebra
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.41.9
@stack 037F

The source-facing equality is retained explicitly.  The finite-fiber
injectivity argument is proof-stage infrastructure; the public surface only
needs the tensor-subalgebra localization statement and its canonical spectrum
ingredients.
-/

/- Lemma 10.41.9: localizing after enlarging the left tensor factor preserves the image in
`Spec R`. -/
@[stacks 037F]
#check @Algebra.TensorProduct.range_comap_localized_subalgebra_eq

@[stacks 037F "localization range owner"]
#check @PrimeSpectrum.localization_away_comap_range

@[stacks 037F "basic-open image owner"]
#check @PrimeSpectrum.mem_image_comap_basicOpen

@[stacks 037F "nilpotence localization owner"]
#check @IsNilpotent.map_iff
