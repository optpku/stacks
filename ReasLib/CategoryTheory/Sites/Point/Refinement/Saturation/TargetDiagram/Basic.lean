module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Target.Category
public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.Basic

/-!
# Basic directed diagrams of finite-cover saturation targets

This leaf owns component targets, their order-indexed morphisms, and the
underlying directed preorder diagram.  Telescope and completion constructions
live in separate leaves.
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
variable {κ : Type z} [Preorder κ]

/-- The target at one index of a directed target-refinement diagram. -/
abbrev stage (D : κ ⥤ Target.{u, v, q, r'} C) (i : κ) :=
  D.obj i

/-- The target refinement attached to an order comparison in a directed target diagram. -/
abbrev hom (D : κ ⥤ Target.{u, v, q, r'} C)
    {i j : κ} (hij : i ≤ j) : stage D i ⟶ stage D j :=
  D.map (homOfLE hij)

namespace hom

/-- A reflexive transition in a target diagram is the identity target refinement. -/
@[simp]
theorem refl (D : κ ⥤ Target.{u, v, q, r'} C) (i : κ) :
    Target.Diagram.hom D (le_rfl : i ≤ i) = 𝟙 (stage D i) := sorry

/-- Target-diagram transitions compose along chains of indices. -/
@[simp]
theorem comp (D : κ ⥤ Target.{u, v, q, r'} C)
    {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    Target.Diagram.hom D (le_trans hij hjk) =
      Target.Diagram.hom D hij ≫ Target.Diagram.hom D hjk := sorry

namespace toRefinement

/-- Forgetting target packaging sends a reflexive diagram transition to the identity ordered
refinement. -/
@[simp]
theorem refl (D : κ ⥤ Target.{u, v, q, r'} C) (i : κ) :
    (Target.Diagram.hom D (le_rfl : i ≤ i)).toRefinement =
      OrderedRefinement.id (stage D i).diagram := sorry

/-- Forgetting target packaging preserves composition of ordered-refinement transitions. -/
@[simp]
theorem comp (D : κ ⥤ Target.{u, v, q, r'} C)
    {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    (Target.Diagram.hom D (le_trans hij hjk)).toRefinement =
      (Target.Diagram.hom D hij).toRefinement.comp
        (Target.Diagram.hom D hjk).toRefinement := sorry

end toRefinement

end hom

/-- Forget the target packaging from a directed target diagram while retaining exactly the
directed systems and ordered-refinement transitions used by the telescope owner. -/
noncomputable def toPreorder (D : κ ⥤ Target.{u, v, q, r'} C) :
    DirectedPreorderSystem.StageDiagram κ C where
  obj := fun i => (stage D i).system
  map := fun hij => (hom D hij).toRefinement
  map_refl := hom.toRefinement.refl D
  map_comp := hom.toRefinement.comp D

namespace toPreorder

/-- Forgetting target packaging retains the directed system at each diagram component. -/
@[simp]
theorem obj (D : κ ⥤ Target.{u, v, q, r'} C) (i : κ) :
    (toPreorder D).obj i = (stage D i).system := sorry

/-- Forgetting target packaging retains the ordered refinement at each transition. -/
@[simp]
theorem map (D : κ ⥤ Target.{u, v, q, r'} C)
    {i j : κ} (hij : i ≤ j) :
    (toPreorder D).map hij = (hom D hij).toRefinement := sorry

namespace map

/-- A reflexive target-diagram transition is the identity refinement. -/
theorem refl (D : κ ⥤ Target.{u, v, q, r'} C) (i : κ) :
    (Target.Diagram.toPreorder D).map (le_rfl : i ≤ i) =
      OrderedRefinement.id (stage D i).diagram := sorry

/-- Target-diagram transitions compose as ordered refinements. -/
theorem comp (D : κ ⥤ Target.{u, v, q, r'} C)
    {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    (Target.Diagram.toPreorder D).map (le_trans hij hjk) =
      ((Target.Diagram.toPreorder D).map hij).comp
        ((Target.Diagram.toPreorder D).map hjk) := sorry

end map

end toPreorder

end Target.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
