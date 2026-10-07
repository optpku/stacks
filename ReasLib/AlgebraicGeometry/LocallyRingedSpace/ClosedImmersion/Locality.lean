module

public import Mathlib.Topology.Sets.OpenCover
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenRestriction

/-!
# Target locality of closed immersions

Closed immersions of locally ringed spaces may be restricted to target opens and detected on an
open cover. The predicate `OnOpen f U` records a closed-immersion restriction of `f` over the
open `U`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion

variable {X Z : LocallyRingedSpace.{u}}

/-- A morphism is a closed immersion over a target open when its restriction to the inverse-image
open can be represented by a closed-immersion restriction morphism. -/
@[stacks 01HL "closed immersion over a target open"]
def OnOpen (f : Z ⟶ X) (U : Opens X) : Prop :=
  ∃ fU : Z.restrict (f.preimageOpen U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding,
    f.IsOpenRestriction (f.preimageOpen U) U fU ∧ IsClosedImmersion fU

/-- `OnOpen f U` is equivalent to the canonical inverse-image restriction of `f` over `U` being a
closed immersion. -/
@[simp, stacks 01HL "canonical inverse-image restriction criterion"]
theorem onOpen_iff (f : Z ⟶ X) (U : Opens X) :
    OnOpen f U ↔ IsClosedImmersion (f.restrictToPreimageOpen U) := sorry

/-- Restricting a closed immersion to a target open preserves closed immersion for the canonical
inverse-image restriction. -/
@[stacks 01HL "restriction of a closed immersion", instance]
theorem restrict (f : Z ⟶ X) [IsClosedImmersion f] (U : Opens X) :
    IsClosedImmersion (f.restrictToPreimageOpen U) := sorry

/-- Any morphism satisfying the restriction relation for a closed immersion is itself a closed
immersion. -/
theorem restrict_of_isOpenRestriction {f : Z ⟶ X} [IsClosedImmersion f] {U : Opens X}
    {fU : Z.restrict (f.preimageOpen U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding}
    (hfU : f.IsOpenRestriction (f.preimageOpen U) U fU) :
    IsClosedImmersion fU := sorry

/-- Closed immersion can be checked on a chosen open cover of the target. -/
@[stacks 01HL]
theorem of_isOpenCover (f : Z ⟶ X)
    {iota : Type v} (U : iota → Opens X) (hU : IsOpenCover U)
    (hclosed : ∀ i, IsClosedImmersion (f.restrictToPreimageOpen (U i))) :
    IsClosedImmersion f := sorry

/-- Closed immersion is equivalent to the canonical inverse-image restriction being a closed
immersion over every member of a chosen target-open cover. -/
@[stacks 01HL]
theorem iff_of_isOpenCover (f : Z ⟶ X)
    {iota : Type v} (U : iota → Opens X) (hU : IsOpenCover U) :
    IsClosedImmersion f ↔
      ∀ i, IsClosedImmersion (f.restrictToPreimageOpen (U i)) := sorry

/-- Being a closed immersion is local on the target for arbitrary open covers. -/
@[stacks 01HL]
theorem iff_exists_openCover (f : Z ⟶ X) :
    IsClosedImmersion f ↔
      ∃ (iota : Type v) (U : iota → Opens X),
        IsOpenCover U ∧
          ∀ i, IsClosedImmersion (f.restrictToPreimageOpen (U i)) := sorry

end AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion
