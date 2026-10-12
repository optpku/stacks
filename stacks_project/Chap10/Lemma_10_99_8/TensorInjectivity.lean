/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Ideal.Flip
import StacksCheckRecall

/-!
# Tensor injectivity support for Lemma 10.99.8

The quotient-first `Tor₁` hypothesis is canonically equivalent to injectivity of ideal tensor
multiplication. This support file recalls the shared equivalence instead of maintaining a
chapter-local one-way wrapper.

@stack 051C
-/

@[expose] public section

/- Lemma 10.99.8 support: injectivity of `I.tensorMul M` is equivalent to vanishing of
`Tor₁[A](A ⧸ I, M)`. -/
@[stacks 051C "quotient-first Tor criterion"]
#check @CategoryTheory.ModuleCat.Tor.isZero_oneQuotientFirst_iff

/- The canonical ideal tensor multiplication map used by the criterion. -/
#check @Ideal.tensorMul
