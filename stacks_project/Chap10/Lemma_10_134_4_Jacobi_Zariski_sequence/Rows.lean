module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

@[expose] public section

/-!
This support module recalls the canonical cotangent-presentation rows used around
Lemma 10.134.4. The former range-restricted `ShortComplex` declarations were proof-local
repackagings with no consumers.
-/

#check @Algebra.Extension.exact_cotangentComplex_toKaehler
#check @Algebra.Extension.toKaehler_surjective
#check @Algebra.Extension.exact_hCotangentι_cotangentComplex
