/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Topology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

/- Lemma 26.18.5: the residue-field fiber square and the stalk-base-change square remain
pullbacks on underlying spaces. -/
@[stacks 01K1] #check Scheme.Pullback.fiber_isPullback_toTop
@[stacks 01K1] #check Scheme.Pullback.fromSpecStalk_isPullback_toTop

/- The horizontal embedding consequences and generic one-sided criteria are reusable glue. -/
#check (f.fiberι s).isEmbedding
#check (pullback.snd (S.fromSpecStalk s) f).isEmbedding
#check IsPreimmersion.isPullback_toTop_of_right
#check IsPreimmersion.isPullback_toTop_of_left

end AlgebraicGeometry
