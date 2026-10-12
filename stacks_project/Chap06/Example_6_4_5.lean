/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Pointwise.DirectSum
import StacksCheckRecall

@[expose] public section

open scoped TopCat

universe u v

variable {X : TopCat.{u}} (M : X → Type v) [∀ x, AddCommGroup (M x)]

/- Example 6.4.5: the assignment sending an open set `U` to the direct sum `⨁_{x ∈ U} M x`,
with restriction maps obtained by discarding summands supported outside the smaller open set,
defines a presheaf of abelian groups. -/
@[stacks 006L]
#check TopCat.Presheaf.PointwiseDirectSum.presheaf M
