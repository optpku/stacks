/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Separation.DisjointCover
import StacksCheckRecall

@[expose] public section

/- Lemma 5.22.4: Mathlib's stronger finite nonempty disjoint-clopen
refinement theorem supplies the source refinement statement. -/
@[stacks 08ZZ "finite disjoint clopen refinements of profinite open covers"]
#check TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover
