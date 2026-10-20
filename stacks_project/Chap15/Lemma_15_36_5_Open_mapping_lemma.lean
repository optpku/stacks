module

public import ReasLib.Topology.Algebra.OpenMapping
import StacksCheckRecall

/-!
# Lemma 15.36.5 (Open mapping lemma) (0CQW)

@stack 0CQW
-/

@[expose] public section

open scoped Topology

universe u v

/- Lemma 15.36.5 (Open mapping lemma) (0CQW): exactly one of openness and a
nowhere-dense image of an open subgroup occurs. -/
@[stacks 0CQW]
#check (@ContinuousAddMonoidHom.isOpenMap_xor_exists_nowhereDense_image :
  ∀ {N : Type u} {M : Type v} [TopologicalSpace N] [AddCommGroup N]
    [TopologicalSpace M] [AddCommGroup M]
    [IsTopologicalAddGroup N] [IsLinearTopology ℤ N]
    [(nhds (0 : N)).IsCountablyGenerated]
    [@CompleteSpace N (IsTopologicalAddGroup.rightUniformSpace N)]
    [IsTopologicalAddGroup M] [T2Space M] (u : N →ₜ+ M),
      Xor (IsOpenMap u)
        (∃ U : OpenAddSubgroup N, IsNowhereDense (u '' (U : Set N))))
