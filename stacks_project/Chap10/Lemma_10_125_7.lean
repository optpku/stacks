module

import StacksCheckRecall
public import ReasLib.RingTheory.KrullDimension.Relative.BaseChange

@[expose] public section

/-!
# Relative-dimension base-change recall

The bounded relative-dimension locus is owned by `RelativeDimensionAtLELocus`.
Its tensor-product base-change formula is independent of the closed-fiber
identifications used to prove it, so that proof plumbing belongs in the shared
library rather than in this source-facing file.

@stack 00QI
-/

/- Lemma 10.125.7, tag 00QI: for a finite-type `R`-algebra `S` and an arbitrary base change
`R → R'`, the preimage of `relativeDimensionAtLELocus R S n` along
`Spec (R' ⊗[R] S) → Spec S` is `relativeDimensionAtLELocus R' (R' ⊗[R] S) n`. -/
@[stacks 00QI "base change of the bounded relative-dimension locus"]
#check @RelativeDimensionAtLELocus.preimage_includeRight_eq_baseChange
