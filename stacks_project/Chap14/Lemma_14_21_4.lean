module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Dimension
import StacksCheckRecall

/-!
@stack 018O
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe u

namespace SSet.Truncated

variable (m : ℕ) (U : SSet.Truncated.{u} m)
variable {n : ℕ} (h : m < n) (x : ((Truncated.sk m).obj U) _⦋n⦌)

/- Lemma 14.21.4 (018O), canonical form: the left extension of an `m`-truncated simplicial set
has dimension at most `m`. -/
@[stacks 018O]
#check (inferInstance : ((Truncated.sk m).obj U).HasDimensionLE m)

/- Lemma 14.21.4 (018O), pointwise form: every simplex in degree strictly above `m` is
degenerate. -/
@[stacks 018O "pointwise degeneracy"]
#check (sk.mem_degenerate_of_lt U h x :
  x ∈ ((Truncated.sk m).obj U).degenerate n)

end SSet.Truncated
