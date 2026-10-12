/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Subset
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {Z : Set X}

/- Lemma 6.32.1: the stalk comparison at points of a closed subset, terminality outside it, and
the pullback-pushforward counit are all owned by the subset-inclusion sheaf formalism. -/
@[stacks 00AE "stalks at points of the closed subset agree with the original stalks"]
#check TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing

@[stacks 00AE "set-valued pushforward stalks outside the closed subset are singletons"]
#check TopCat.Sheaf.ClosedSubset.type_stalk_isTerminal_of_not_mem

@[stacks 00AE "the pullback-pushforward counit for a closed-subset inclusion is an isomorphism"]
#check TopCat.Sheaf.Subset.counit_isIso

@[stacks 00AE "algebraic-structure-valued pushforward stalks outside the closed subset are final"]
#check TopCat.Sheaf.ClosedSubset.stalk_isTerminal_of_not_mem

@[stacks 00AE "abelian pushforward stalks outside the closed subset are zero"]
#check TopCat.Sheaf.ClosedSubset.AddCommGrp.stalk_isZero_of_not_mem
