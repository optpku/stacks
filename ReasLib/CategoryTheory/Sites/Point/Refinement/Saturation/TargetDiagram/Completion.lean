/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Telescope

/-!
# Completion of directed target diagrams

This leaf states the target-side eventual-realization condition and its
completion consequence for the canonical telescope target.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Target.Diagram

variable {C : Type u} [Category.{v} C]
variable [LocallySmall.{q} C]
variable {J : GrothendieckTopology C}
variable {κ : Type z} [Preorder κ] [IsDirectedOrder κ]

/-- Every request at a component target is eventually realized along a directed target diagram. -/
def eventuallyRealizes (D : κ ⥤ Target.{u, v, q, r'} C) : Prop :=
  ∀ a : κ, ∀ request : (stage D a).Request J,
    ∃ b : κ, ∃ hab : a ≤ b, ((hom D hab).mapRequest request).is_realized

namespace TelescopeTarget

variable {D : κ ⥤ Target.{u, v, q, r'} C}

/-- Eventual realization in a directed target diagram makes its telescope target finite-cover
complete.  No source-stage anchor is needed because this conclusion concerns only the target. -/
theorem complete_of_eventuallyRealizes (target : TelescopeTarget D)
    (h_eventual : eventuallyRealizes (J := J) D) :
    target.toTarget.complete J := sorry

end TelescopeTarget

end Target.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
