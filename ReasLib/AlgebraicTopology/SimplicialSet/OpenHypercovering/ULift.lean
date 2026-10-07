module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Definition
public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Universe lifting for open hypercoverings

The simplicial index and the carrier of an open family may live in different universes.  This
leaf transports the base space along the canonical `ULift` homeomorphism, so the topological-space
and cohomological-descent leaves can consume the output of the basis constructors without a manual
universe rebuild.
-/

@[expose] public section

open TopologicalSpace

universe u v

namespace SSet

variable {X : Type u} [TopologicalSpace X] {I : SSet.{v}}

namespace OpenFamily

/-- Transport an indexed open family along the canonical homeomorphism
`X ≃ₜ ULift.{v} X`. -/
@[stacks 01H1 "universe-lifted indexed open family"]
noncomputable def ulift (U : OpenFamily X I) :
    OpenFamily (ULift.{v} X) I where
  openAt := fun i => Homeomorph.ulift.{v, u}.symm.opensCongr (U.openAt i)
  map_le := sorry

/-- The lifted family computes pointwise by transporting its open along the canonical
homeomorphism. -/
@[simp]
theorem ulift_openAt (U : OpenFamily X I) {Delta : SimplexCategoryᵒᵖ}
    (i : I.obj Delta) :
    U.ulift.openAt i = Homeomorph.ulift.{v, u}.symm.opensCongr (U.openAt i) := rfl

end OpenFamily

namespace OpenHypercovering

/-- Transport an open hypercovering along `X ≃ₜ ULift.{v} X`, preserving its simplicial index. -/
@[stacks 01H1 "universe-lifted open hypercovering"]
noncomputable def ulift (H : OpenHypercovering.{u, v} X) :
    OpenHypercovering.{max u v, v} (ULift.{v} X) where
  I := H.I
  family := H.family.ulift
  zero_isOpenCover := sorry
  succ := sorry

@[simp]
theorem ulift_family (H : OpenHypercovering.{u, v} X) :
    H.ulift.family = H.family.ulift := rfl

end OpenHypercovering

end SSet
