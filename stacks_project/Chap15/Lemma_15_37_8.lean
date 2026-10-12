/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.BaseChange
import StacksCheckRecall

/-!
# Lemma 15.37.8 (07EG)

@stack 07EG
-/

@[expose] public section

/- Lemma 15.37.8 (07EG): adic formal smoothness is stable under arbitrary base change. -/
@[stacks 07EG "base change of adic formal smoothness"]
#check @RingHom.formally_smooth_for_adic_baseChange
