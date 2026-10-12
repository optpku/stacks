/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Telescope

/-!
# Cocones for target-refinement telescopes

This leaf packages the canonical component-to-telescope refinements of a
directed target diagram as a standard categorical cocone when the diagram and
component indices share a universe.  The heterogeneous-universe component API
remains available from `TargetDiagram.Telescope`.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Target.Diagram

variable {C : Type u} [Category.{v} C]
variable [LocallySmall.{q} C]
variable {κ : Type r'} [Preorder κ] [IsDirectedOrder κ]

namespace telescopeCocone

/-- Naturality of the standard cocone whose legs are the canonical target
telescope inclusions. -/
theorem naturality
    (D : κ ⥤ Target.{u, v, q, r'} C) (target : TelescopeTarget D)
    {a b : κ} (f : a ⟶ b) :
    D.map f ≫ telescopeInclusion D target b =
      telescopeInclusion D target a ≫
        ((Functor.const κ).obj target.toTarget).map f := sorry

end telescopeCocone

/-- The standard categorical cocone from a directed target-refinement diagram
to its telescope target. -/
noncomputable def telescopeCocone
    (D : κ ⥤ Target.{u, v, q, r'} C) (target : TelescopeTarget D) :
    Cocone D :=
  Cocone.mk target.toTarget {
    app := telescopeInclusion D target
    naturality := fun _ _ f => telescopeCocone.naturality D target f
  }

namespace telescopeCocone

/-- The vertex of the target telescope cocone is its telescope target. -/
@[simp]
theorem pt
    (D : κ ⥤ Target.{u, v, q, r'} C) (target : TelescopeTarget D) :
    (telescopeCocone D target).pt = target.toTarget := sorry

/-- A component of the target telescope cocone is the canonical telescope
inclusion at that index. -/
@[simp]
theorem ιApp
    (D : κ ⥤ Target.{u, v, q, r'} C) (target : TelescopeTarget D) (a : κ) :
    (telescopeCocone D target).ι.app a = telescopeInclusion D target a := sorry

end telescopeCocone

/- The cocone has explicit point and leg data; `sorryAx` is confined to its
naturality proof field. -/

end Target.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
