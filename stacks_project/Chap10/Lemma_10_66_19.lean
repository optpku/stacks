/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.BaseChange.Textbook
import StacksCheckRecall

@[expose] public section

/-! @stack 0CUB -/

/-!
# Lemma 10.66.19

The reusable owner is
`weaklyAssociatedPrimes.BaseChange.under_mem`: it uses the canonical base-change
module `(R ⊗[k] K) ⊗[R] M`.  The source-facing tensor bridge is owned by
`weaklyAssociatedPrimes.BaseChange.Textbook`; consumers opt into its scoped
`TensorProduct.Right` action rather than changing global instance search.
-/

/- Lemma 10.66.19 (Tag 0CUB): the source conclusion is represented by the
canonical base-change module `(R ⊗[k] K) ⊗[R] M`; contracting a weakly associated
prime to `R` preserves weak association. -/
@[stacks 0CUB]
#check @weaklyAssociatedPrimes.BaseChange.under_mem

@[stacks 0CUB]
#check @weaklyAssociatedPrimes.BaseChange.Textbook.under_mem

#check @weaklyAssociatedPrimes.BaseChange.Textbook.eq_canonical
#check @weaklyAssociatedPrimes.BaseChange.Textbook.toOwner
