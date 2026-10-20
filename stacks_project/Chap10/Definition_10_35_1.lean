/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.35.1

@stack 00G0
-/

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 10.35.1 is recalled canonically by `IsJacobsonRing R`: a commutative ring is Jacobson
if every radical ideal is the intersection of the maximal ideals containing it, equivalently if
every radical ideal equals its Jacobson radical.
-/
@[stacks 00G0 "Jacobson ring predicate"]
#check @IsJacobsonRing

/- Companion recall: the defining radical-ideal formulation is the canonical equivalence
`isJacobsonRing_iff`. -/
@[stacks 00G0 "radical-ideal characterization"]
#check @isJacobsonRing_iff
