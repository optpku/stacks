/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Tate
import StacksCheckRecall

@[expose] public section

/-!
# Tate's Criterion for Japanese Domains

@stack 032P

The reusable principal-adic criterion is owned by `IsN2Ring` in `ReasLib`.
-/

-- Lemma 10.161.16 (Tate), tag `032P`: a normal Noetherian domain which is complete for a
-- principal ideal is `N-2` when the corresponding quotient is an `N-2` domain.
@[stacks 032P]
#check @IsN2Ring.of_principalAdicComplete
