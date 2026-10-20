module

public import ReasLib.RingTheory.Spectrum.Prime.Polynomial.UnitLeadingCoeff
import StacksCheckRecall

/-!
# Lemma 10.29.9

@stack 00FD
-/

@[expose] public section

-- Lemma 10.29.9: when the leading coefficient of `g` is a unit, the image of
-- `D(f) ∩ V(g)` is a finite union of basic opens.
@[stacks 00FD "source finite-basic-open cover"]
#check @Polynomial.UnitLeadingCoeff.exists_iUnion_basicOpen

@[stacks 00FD "unit-leading-coefficient canonical owner"]
#check @Polynomial.exists_image_comap_of_isUnit_leadingCoeff

@[stacks 00FD "unit-leading-coefficient compactness"]
#check @Polynomial.isCompact_image_comap_of_isUnit_leadingCoeff

@[stacks 00FD "unit-leading-coefficient openness"]
#check @Polynomial.isOpen_image_comap_of_isUnit_leadingCoeff
