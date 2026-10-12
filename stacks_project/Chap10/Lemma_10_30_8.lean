/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.GoingUp.Algebraic
public import ReasLib.RingTheory.Localization.FractionRing.Algebraic
public import ReasLib.RingTheory.Spectrum.Prime.ZeroLocus.Image
import StacksCheckRecall

/-!
# Algebraic fraction fields and zero-locus images

@stack 0H7L
-/

@[expose] public section

@[stacks 0H7L "algebraicity descends from fraction rings"]
#check @Algebra.IsAlgebraic.of_isFractionRing

@[stacks 0H7L "(1), nonzero ideal contraction"]
#check @Algebra.IsAlgebraic.comap_ne_bot

@[stacks 0H7L "zero contraction criterion"]
#check @Algebra.IsAlgebraic.eq_bot_of_comap_eq_bot

@[stacks 0H7L "density criterion"]
#check @PrimeSpectrum.dense_image_comap_zeroLocus_iff

@[stacks 0H7L "(2), nondense zero-locus image"]
#check @PrimeSpectrum.not_dense_image_comap_zeroLocus

@[stacks 0H7L "reduced-base nondensity criterion"]
#check @PrimeSpectrum.not_dense_image_comap_zeroLocus_iff
