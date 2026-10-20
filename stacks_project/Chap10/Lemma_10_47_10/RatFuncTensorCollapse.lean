module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.FieldTheory.RatFunc.FieldExtension
public import ReasLib.RingTheory.Spectrum.Prime.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Rational-function tensor support

The old chapter-local tensor/localization RingEquiv chain was proof plumbing for Lemma 10.47.10
and had no downstream consumer.  The theorem is now owned by the RatFunc field-extension leaf;
this compatibility module only points users to the canonical map and ring-level localization API.

@stack 0G31
-/

/- Canonical coefficient extension. -/
@[stacks 0G31]
#check @RatFunc.FieldExtension.map

/- Irreducibility after localization. -/
@[stacks 0G31]
#check @PrimeSpectrum.irreducible_of_isLocalization

/- Standard tensor base-change equivalence. -/
@[stacks 0G31 "tensor base-change equivalence"]
#check @Algebra.TensorProduct.cancelBaseChange

end
