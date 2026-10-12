/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Types.FilterGerm
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Filter TopCat
open CategoryTheory.Limits
open scoped Topology

universe u

noncomputable section

/- The sheaf itself is the canonical `TopCat.sheafToTypes`.  Its generic stalkwise evaluation
API is owned by `Topology.Sheaves.Types.Stalks`; this item only recalls the source-facing map. -/

section

variable {X : TopCat.{u}} (A : X → Type u) (x : X)

/- Example 6.11.5 (1): for the sheaf `U ↦ ∏ y : U, A y`, evaluation at `x` induces a canonical
map from its stalk at `x` to the fiber `A x`. -/
@[stacks 007D "evaluation from the stalk to the pointwise fiber"]
#check TopCat.dependentFunctionStalkToFiber A x

end

section

variable {X : TopCat.{u}} {x : X}
variable (f : ℕ → X) (h_tendsto : Tendsto f atTop (nhds x))

/- The shared owner is formulated for an arbitrary filter, map, and dependent function family.
This example specializes it to the `atTop` filter on `ℕ` and the constant binary family. -/

/- Example 6.11.5 (2): if `f n → x` and the points `f n` are pairwise distinct, then the
binary-function stalk maps onto the tails of binary sequences. -/
#check (TopCat.FunctionStalk.toGerm (ULift.{u} Bool) f h_tendsto)

@[stacks 007D "surjection from the binary-function stalk onto binary tails"]
#check fun h_injective : Function.Injective f ↦
  TopCat.FunctionStalk.toGerm_surjective_of_injective (ULift.{u} Bool) f h_tendsto h_injective

/- Example 6.11.5 (3): the set of tails of binary sequences is infinite. -/
@[stacks 007D "binary tails form an infinite set"]
#check fun [hB : Nontrivial (ULift.{u} Bool)] ↦
  @Filter.Germ.infinite_atTop_of_nontrivial (ULift.{u} Bool) hB

/- Example 6.11.5 (4): the evaluation map on the binary-function stalk is not injective under the
convergent, pairwise-distinct sequence hypotheses. -/
@[stacks 007D "the stalk-to-fiber evaluation need not be injective"]
#check fun [hB : Nontrivial (ULift.{u} Bool)] (h_injective : Function.Injective f) ↦
  @TopCat.FunctionStalk.toFiber_not_injective_of_tendsto_injective
    _ _ (ULift.{u} Bool) hB f h_tendsto h_injective

end

section

variable {X : TopCat.{u}} (A : X → Type u) (x : X)

/- Example 6.11.5 (5): if every open neighborhood of `x` contains a point whose fiber is empty,
then the stalk at `x` of the dependent-function sheaf is empty. -/
@[stacks 007D "empty fibers arbitrarily near the point force an empty stalk"]
#check TopCat.isEmpty_stalk_of_exists_empty_fiber_in_every_openNhds A x

end
