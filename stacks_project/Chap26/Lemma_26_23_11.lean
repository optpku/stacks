/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.ProductSpectrum.SigmaSpec.FieldSpectra

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.23.11 (1): every monomorphism into the spectrum of a finite product of fields is,
over the target, the inclusion of the factors indexed by a subset. -/
@[stacks 03DP] #check
  Scheme.ProductSpectrum.FieldSpectra.exists_subset_isoOver_of_mono
#check Scheme.ProductSpectrum.FieldSpectra.subobject_eq_support
#check Scheme.ProductSpectrum.FieldSpectra.subobjectEquivSet
#check Scheme.ProductSpectrum.FieldSpectra.support_isoOver_of_mono
#check Scheme.ProductSpectrum.FieldSpectra.exists_iso_support
#check Scheme.ProductSpectrum.FieldSpectra.support_eq_of_isoOver
#check Scheme.ProductSpectrum.FieldSpectra.exists_subset_iso_of_mono

/- Lemma 26.23.11 (2): every monomorphism into an arbitrary coproduct of field spectra is,
over the target, the inclusion of the summands indexed by a subset. -/
@[stacks 03DP] #check
  Scheme.Coproduct.FieldSpectra.exists_subset_isoOver_of_mono
#check Scheme.Coproduct.FieldSpectra.subobject_eq_support
#check Scheme.Coproduct.FieldSpectra.subobjectEquivSet
#check Scheme.Coproduct.FieldSpectra.support_isoOver_of_mono
#check Scheme.Coproduct.FieldSpectra.exists_iso_support
#check Scheme.Coproduct.FieldSpectra.support_eq_of_isoOver
#check Scheme.Coproduct.FieldSpectra.exists_subset_iso_of_mono

/- The uniqueness of an isomorphism over a monomorphism is inherited from the generic slice API. -/
#check @CategoryTheory.Over.isoSubsingletonOfMono

/- In the finite same-universe case, the product and coproduct presentations agree under the
canonical `sigmaSpec` identification. -/
#check Scheme.ProductSpectrum.sigmaSpecIso
#check Scheme.ProductSpectrum.coproduct_support_toCoproduct
#check Scheme.ProductSpectrum.subobjectOrderIso
#check Scheme.ProductSpectrum.subobjectOrderIso_mk
#check Scheme.ProductSpectrum.FieldSpectra.subobjectEquivSet_sigmaSpec
#check Scheme.ProductSpectrum.FieldSpectra.subobjectSupport_sigmaSpec
#check Scheme.ProductSpectrum.FieldSpectra.subobjectEquivSet_sigmaSpec_symm
#check Scheme.ProductSpectrum.FieldSpectra.subobjectSupport_sigmaSpec_symm
