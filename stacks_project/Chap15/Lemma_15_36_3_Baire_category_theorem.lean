/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Algebra.Baire
import StacksCheckRecall

/-!
Lemma 15.36.3 (Baire category theorem) (0CQU): a complete linearly topologized abelian group with
a countable fundamental system of neighborhoods of zero satisfies the Baire category theorem.

@stack 0CQU
-/

@[expose] public section

open scoped Topology

universe u

section

variable {M : Type u} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  [IsLinearTopology ℤ M] [(nhds (0 : M)).IsCountablyGenerated]
  [@CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)]
variable {U : ℕ+ → Set M}

/- Lemma 15.36.3 (Baire category theorem) (0CQU), with the source's linear-topology hypothesis. -/
@[stacks 0CQU]
#check
  (dense_iInter_open_of_complete_linearlyTopologizedAddGroup
      (U := U) :
    (∀ n, IsOpen (U n)) → (∀ n, Dense (U n)) → Dense (⋂ n, U n))

/- Stronger reusable bridge used by the following open-mapping lemmas. -/
#check @dense_iInter_open_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup
#check @baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup

end
