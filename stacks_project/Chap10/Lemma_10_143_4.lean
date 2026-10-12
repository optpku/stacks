/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Field
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.143.4

@stack 00U3
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.143.4: for a field `k`, a `k`-algebra `S` is étale over `k` if and only if `S` is
isomorphic as a `k`-algebra to a finite product of finite separable field extensions of `k`. This
is exactly the canonical theorem `Algebra.Etale.iff_exists_algEquiv_prod`. -/
@[stacks 00U3 "etale algebras over a field"]
#check @Algebra.Etale.iff_exists_algEquiv_prod
