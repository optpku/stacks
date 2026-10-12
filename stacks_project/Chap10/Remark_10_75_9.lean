/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Ideal
import StacksCheckRecall

/-!
# Remark 10.75.9

@stack 00M6
-/

@[expose] public section

/- Remark 10.75.9 [stacks 00M6]: canonical recall of the shared proposition-level
criterion for degree-one `Tor` of an ideal quotient.  The reusable owner is
`CategoryTheory.ModuleCat.Tor.isZero_oneQuotient_iff`; it uses the canonical map
`Ideal.tensorMul` and does not expose a chosen quotient-kernel equivalence. -/

@[stacks 00M6]
#check @CategoryTheory.ModuleCat.Tor.isZero_oneQuotient_iff
