module

public import ReasLib.Topology.Algebra.Baire
import Mathlib.Tactic.CrossRefAttribute

/-!
# Open mapping for linearly topologized additive groups

This leaf records the open-mapping dichotomy for continuous homomorphisms from complete,
countably based, linearly topologized abelian groups.

@stack 0CQW
-/

@[expose] public section

open scoped Topology

universe u v

namespace ContinuousAddMonoidHom

variable {N : Type u} {M : Type v}
variable [TopologicalSpace N] [AddCommGroup N] [IsTopologicalAddGroup N]
  [IsLinearTopology ℤ N] [(nhds (0 : N)).IsCountablyGenerated]
  [@CompleteSpace N (IsTopologicalAddGroup.rightUniformSpace N)]
variable [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [T2Space M]

/-- Lemma 15.36.5 (Open mapping lemma) (0CQW): a continuous homomorphism from a complete
linearly topologized abelian group with a countable fundamental system of neighborhoods of zero
to a separated topological abelian group is open exactly when no open subgroup has nowhere-dense
image. -/
@[stacks 0CQW "Open mapping lemma"]
theorem isOpenMap_xor_exists_nowhereDense_image (u : N →ₜ+ M) :
    Xor (IsOpenMap u)
      (∃ U : OpenAddSubgroup N, IsNowhereDense (u '' (U : Set N))) := sorry

end ContinuousAddMonoidHom
