/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Existence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.127.18

@stack 00R1
-/

/- Lemma 10.127.18 [stacks 00R1]: a finitely presented module over a finitely
presented ring homomorphism admits a compatible directed finite-module
approximation.  This is owned by
`Ring.DirectLimit.Algebra.Approximation.Module.exists_of_finitePresentation`;
the chapter records the source theorem by recalling the reusable API directly. -/
@[stacks 00R1 "finite module approximation existence"]
#check @Ring.DirectLimit.Algebra.Approximation.Module.exists_of_finitePresentation
