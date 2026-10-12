/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Square

/-!
# Equation 15.5.3.1

@stack 0D2E

The source functor sends a module over the upper-left ring of a commutative square to
its two extensions of scalars together with the canonical comparison.  This is exactly
`ModuleCat.extendScalarsToPullback`.
-/

open CategoryTheory

/- 15.5.3.1 (0D2E): the canonical functor from modules over the corner ring to the
categorical pullback of the two module categories. -/
@[stacks 0D2E "15.5.3.1 canonical module base-change functor"]
#check @ModuleCat.extendScalarsToPullback

@[stacks 0D2E "canonical commuting-square data"]
#check @ModuleCat.extendScalarsCommSq
