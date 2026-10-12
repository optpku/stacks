/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Product.Basis
import StacksCheckRecall

@[expose] public section

/-!
# Product-of-fields support for Lemma 10.78.8

The product-of-fields basis step is owned by the reusable `ReasLib` linear-algebra API.

@stack 03C1
-/

/- Lemma 10.78.8, tag `03C1`: a spanning subspace of a finite product of field-valued free
modules contains a basis over the product ring. -/
@[stacks 03C1 "product-of-fields basis step"]
#check @Module.Basis.exists_mem_of_span_eq_top_pi
