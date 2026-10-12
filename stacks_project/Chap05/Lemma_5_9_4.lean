/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.NoetherianSpace
import StacksCheckRecall

@[expose] public section

/-
`TopologicalSpace.NoetherianSpace.iUnion` is the canonical finite-union theorem: it uses an
arbitrary finite index type rather than a chosen enumeration `Fin n`. Taking `ι := Fin n`
recovers the source, while canonical finite indexing supports reuse without a local wrapper.
-/

/- Lemma 5.9.4: if `X` is a topological space and `Xᵢ ⊆ X` is a finite family of subsets such
that each `Xᵢ` is Noetherian with the induced topology, then the union `⋃ i, Xᵢ` is Noetherian
with the induced topology. -/
@[stacks 0053 "finite unions of Noetherian subspaces"]
#check TopologicalSpace.NoetherianSpace.iUnion
