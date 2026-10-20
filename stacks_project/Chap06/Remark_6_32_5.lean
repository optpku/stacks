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

universe u

variable {X : TopCat.{u}} {Z : Set X}

/- Remark 6.32.5: failure of coproduct preservation, right exactness, and existence of a right
adjoint are properties of the closed-subset pushforward functor, not chapter-local examples. -/
@[stacks 00AI "set-valued pushforward does not preserve binary coproducts"]
#check TopCat.Sheaf.ClosedSubset.not_preservesBinaryCoproducts

@[stacks 00AI "set-valued pushforward is not right exact"]
#check TopCat.Sheaf.ClosedSubset.not_rightExact

@[stacks 00AI "set-valued pushforward has no right adjoint"]
#check TopCat.Sheaf.ClosedSubset.not_isLeftAdjoint
