module

public import ReasLib.Topology.Sheaves.Pointwise.DirectSum
import StacksCheckRecall

@[expose] public section
universe u v

noncomputable section

variable {X : TopCat.{u}}

section

variable (M : X → Type v) [∀ x, AddCommGroup (M x)]

/- Example 6.7.6 (1): on an infinite discrete space, the pointwise direct-sum presheaf
with constant fiber `ℤ` does not satisfy the sheaf condition.  This is the `ℤ` specialization of
the shared nontrivial-fiber theorem. -/
section

variable [DiscreteTopology X] [Infinite X]

@[stacks 006Y "the pointwise direct-sum presheaf is not a sheaf in general"]
#check
  (TopCat.Presheaf.PointwiseDirectSum.not_isSheaf_of_infinite_discrete
    (X := X) (M := fun _ : X ↦ ℤ))

end

/- Example 6.7.6 (2): if every open subset of `X` is quasi-compact, then the pointwise direct-sum
presheaf from Example 6.4.5 satisfies the sheaf condition. -/
@[stacks 006Y "compact opens make the pointwise direct-sum presheaf a sheaf"]
recall TopCat.Presheaf.PointwiseDirectSum.isSheaf_of_compact_opens

end
