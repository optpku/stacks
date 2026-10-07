module

public import ReasLib.AlgebraicGeometry.AffineScheme.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/- Lemma 26.6.7: affine schemes have finite limits, these limits are computed
in locally ringed spaces, and affine pullbacks are spectra of tensor
products. -/
@[stacks 01I4] #check (inferInstance : HasFiniteLimits AffineScheme)
@[stacks 01I4 "forgetful functor preserves finite limits"]
#check (inferInstance : PreservesFiniteLimits
  (AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace))
@[stacks 01I4 "products of affine spectra"] #check prodSpecIso
#check prodSpecIso_inv_fst
#check prodSpecIso_inv_snd
@[stacks 01I4 "fiber products of affine spectra"] #check pullbackSpecIso
#check pullbackSpecIso_inv_fst
#check pullbackSpecIso_inv_snd
