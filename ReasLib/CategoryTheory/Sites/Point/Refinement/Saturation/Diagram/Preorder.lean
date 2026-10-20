/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Diagram.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.Basic

/-!
# Preorder-system diagrams underlying based saturation diagrams

This leaf forgets scheduled-stage data from a based diagram while retaining
the coherent directed-preorder systems and their ordered refinements.  The
basic based-diagram owner does not depend on the generic telescope machinery.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Diagram

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {κ : Type z} [Preorder κ]

namespace hom.toRefinement

/-- Forgetting to ordered refinements sends a reflexive diagram transition to the identity. -/
@[simp]
theorem refl (D : Diagram (J := J) A κ) (i : κ) :
    (D.hom (le_rfl : i ≤ i)).toRefinement =
      OrderedRefinement.id (D.stage i).diagram := sorry

/-- Forgetting to ordered refinements preserves composition of diagram transitions. -/
@[simp]
theorem comp (D : Diagram (J := J) A κ)
    {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    (D.hom (le_trans hij hjk)).toRefinement =
      (D.hom hij).toRefinement.comp (D.hom hjk).toRefinement := sorry

end hom.toRefinement

/-- Forget scheduled-stage data from a based diagram, retaining its reusable diagram of directed
preorder systems. -/
noncomputable def toPreorder (D : Diagram (J := J) A κ) :
  DirectedPreorderSystem.StageDiagram κ C where
  obj := fun i => (D.stage i).system
  map := fun hij => (D.hom hij).toRefinement
  map_refl := hom.toRefinement.refl D
  map_comp := hom.toRefinement.comp D

namespace toPreorder

/-- The preorder-system object underlying a based diagram stage is that stage's directed
preorder system. -/
@[simp]
theorem obj (D : Diagram (J := J) A κ) (i : κ) :
    D.toPreorder.obj i = (D.stage i).system := sorry

/-- The preorder-system transition underlying a based diagram morphism is its ordered
refinement. -/
@[simp]
theorem map (D : Diagram (J := J) A κ)
    {i j : κ} (hij : i ≤ j) :
    D.toPreorder.map hij = (D.hom hij).toRefinement := sorry

namespace map

/-- The pure transition of the preorder-system diagram at a reflexive comparison is the identity
ordered refinement. -/
theorem refl (D : Diagram (J := J) A κ) (i : κ) :
    D.toPreorder.map (le_rfl : i ≤ i) = OrderedRefinement.id (D.stage i).diagram := sorry

/-- The pure transitions of the preorder-system diagram compose along chains of indices. -/
theorem comp (D : Diagram (J := J) A κ)
    {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    D.toPreorder.map (le_trans hij hjk) =
      (D.toPreorder.map hij).comp (D.toPreorder.map hjk) := sorry

end map
end toPreorder

end Stage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
