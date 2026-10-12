/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.AutoAssociated
import StacksCheckRecall

/-!
# Auto-associated rings

@stack 05GM
-/

@[expose] public section

-- Definition 15.15.1: a commutative ring is auto-associated when it is local and its maximal
-- ideal is weakly associated to the regular module.
@[stacks 05GM "Definition 15.15.1"]
#check @IsAutoAssociatedRing

@[stacks 05GM "auto-associated ring criterion"]
#check @isAutoAssociatedRing_iff

@[stacks 05GM "torsion ideal of definition"]
#check @IsAutoAssociatedRing.exists_torsionOf_isIdealOfDefinition
