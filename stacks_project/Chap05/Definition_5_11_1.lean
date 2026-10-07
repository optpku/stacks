module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.Sets.Closeds
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
`TopologicalSpace.IrreducibleCloseds X` bundles exactly the source's irreducible closed subsets,
and its inclusion order makes strict `LTSeries` the stated chains. The theorem
`Order.coheight_eq_iSup_head_eq` identifies `Order.coheight Y` with their supremal length.
Thus the tagged check specializes the canonical order-theoretic owner instead of introducing a
parallel `codim` alias. The global `topologicalKrullDim X` and the upper-interval view
`Order.coheight_eq_krullDim_Ici` remain derived alternatives, while later codimension results can
reuse the standard coheight API directly.
-/

/- Definition 5.11.1: the codimension of an irreducible closed subset `Y` in `X` is the supremum
of the lengths of strict chains of irreducible closed subsets of `X` beginning at `Y`. -/
@[stacks 02I3 "codimension of an irreducible closed subset as its coheight"]
#check fun {X : Type u} [TopologicalSpace X]
    (Y : TopologicalSpace.IrreducibleCloseds X) ↦ Order.coheight Y
