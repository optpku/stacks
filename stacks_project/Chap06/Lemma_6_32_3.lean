/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Subset
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}} {Z : Set X}

/- Lemma 6.32.3: this is the `AddCommGrpCat` specialization of the arbitrary-subset
fully-faithful owner, together with the closed-subset zero-stalk essential-image criterion. -/
@[stacks 00AG "pushforward of abelian sheaves along a closed subset is fully faithful"]
#check TopCat.Sheaf.Subset.fullyFaithful

@[stacks 00AG "essential image consists of abelian sheaves with zero stalks off the closed subset"]
#check TopCat.Sheaf.ClosedSubset.AddCommGrp.essImage_iff_stalk_isZero_of_not_mem
