/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.Away.Powers
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization

/-!
# Radical criteria for affine blowup charts

This leaf owns the chart-level consequences of equality of radicals.  The
radical formulation is the reusable algebraic interface; the zero-locus
formulation is retained as a thin geometric bridge for source-facing uses.
-/

@[expose] public section

universe u

open PrimeSpectrum

namespace AffineBlowupChart

variable {R : Type u} [CommRing R]

/-- A principal ideal with the same radical as the center gives a regular image in the affine
blowup chart. -/
@[stacks 080U "regular element from a radical equality"]
theorem isRegular_of_radical_eq
    (I : Ideal R) (a : I) (f : R)
    (hI : (Ideal.span ({f} : Set R)).radical = I.radical) :
    IsRegular (@algebraMap R (affineBlowupChart I a) _ _ (instAlgebra I a) f) := sorry

/-- If a principal ideal has the same radical as the center, localizing the chart away from its
image is the ordinary localization away from the chart parameter. -/
@[stacks 080U "localization away from a radical-equivalent element"]
theorem isLocalizationAway_of_radical_eq
    (I : Ideal R) (a : I) (f : R)
    (hI : (Ideal.span ({f} : Set R)).radical = I.radical) :
    IsLocalization.Away (@algebraMap R (affineBlowupChart I a) _ _ (instAlgebra I a) f)
      (Localization.Away a.1) := sorry

/-- The regularity criterion in the geometric source form `V(f) = V(I)`. -/
@[stacks 080U "regular element from an equal zero locus"]
theorem isRegular_of_zeroLocus_eq
    (I : Ideal R) (a : I) (f : R)
    (hV : zeroLocus ({f} : Set R) = zeroLocus (I : Set R)) :
    IsRegular (@algebraMap R (affineBlowupChart I a) _ _ (instAlgebra I a) f) := sorry

/-- The localization criterion in the geometric source form `V(f) = V(I)`. -/
@[stacks 080U "localization from an equal zero locus"]
theorem isLocalizationAway_of_zeroLocus_eq
    (I : Ideal R) (a : I) (f : R)
    (hV : zeroLocus ({f} : Set R) = zeroLocus (I : Set R)) :
    IsLocalization.Away (@algebraMap R (affineBlowupChart I a) _ _ (instAlgebra I a) f)
      (Localization.Away a.1) := sorry

end AffineBlowupChart
