/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Separating

/-!
# Separating-stage diagram specialization

This leaf gives ordinary diagrams of separating stages the same component, transition, and
forgetful API as target and refinement-stage diagrams.  It is the neutral intermediate layer
between scheduled stage diagrams and refinement-stage telescopes.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace SeparatingStage.Diagram

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {κ : Type z} [Preorder κ]

/-- The separating stage at one index of an ordinary diagram. -/
abbrev stage (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y) (i : κ) :=
  D.obj i

/-- The separating-stage morphism attached to an order comparison. -/
abbrev hom (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y)
    {i j : κ} (hij : i ≤ j) : stage D i ⟶ stage D j :=
  D.map (homOfLE hij)

namespace hom

/-- A reflexive separating-stage diagram transition is the identity morphism. -/
@[simp]
theorem refl (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y) (i : κ) :
    hom D (le_rfl : i ≤ i) = 𝟙 (stage D i) := sorry

/-- Separating-stage diagram transitions compose along chains of indices. -/
@[simp]
theorem comp (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y)
    {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    hom D (le_trans hij hjk) = hom D hij ≫ hom D hjk := sorry

end hom

/-- Forget separation data componentwise from a diagram of separating stages. -/
noncomputable def toRefinementDiagram
    (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y) :
    κ ⥤ RefinementStage.{u, v, q, r, r'} S :=
  D ⋙ SeparatingStage.forget

namespace toRefinementDiagram

/-- A component of the forgotten diagram is the refinement stage underlying the corresponding
separating stage. -/
@[simp]
theorem obj (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y) (i : κ) :
    (toRefinementDiagram D).obj i = (stage D i).toRefinementStage := sorry

/-- A transition of the forgotten diagram is the refinement-stage morphism underlying the
corresponding separating-stage transition. -/
@[simp]
theorem map (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y)
    {i j : κ} (hij : i ≤ j) :
    (toRefinementDiagram D).map (homOfLE hij) = (hom D hij).toRefinementStage := sorry

namespace map

/-- Forgetting a separating-stage diagram transition preserves its ordered refinement. -/
@[simp]
theorem toRefinement
    (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y)
    {i j : κ} (hij : i ≤ j) :
    ((toRefinementDiagram D).map (homOfLE hij)).toRefinement =
      (hom D hij).toRefinement := sorry

end map

end toRefinementDiagram

/-- Forget a diagram of separating stages to its neutral diagram of finite-cover targets. -/
noncomputable def toTargetDiagram
    (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y) :
    κ ⥤ Target.{u, v, q, r'} C :=
  toRefinementDiagram D ⋙ RefinementStage.forget

namespace toTargetDiagram

/-- The target component is the target carried by the corresponding separating stage. -/
@[simp]
theorem obj (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y) (i : κ) :
    (toTargetDiagram D).obj i = (stage D i).target := sorry

/-- A target transition is the fully forgotten separating-stage transition. -/
@[simp]
theorem map (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y)
    {i j : κ} (hij : i ≤ j) :
    (toTargetDiagram D).map (homOfLE hij) = (hom D hij).toRefinementStage.toTarget := sorry

/-- Forgetting a separating-stage transition to targets preserves its ordered refinement. -/
@[simp]
theorem map.toRefinement
    (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y)
    {i j : κ} (hij : i ≤ j) :
    ((toTargetDiagram D).map (homOfLE hij)).toRefinement =
      (hom D hij).toRefinement := sorry

/-- The target diagram factors through the neutral refinement-stage diagram. -/
theorem factorization
    (D : κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y) :
    toTargetDiagram D = toRefinementDiagram D ⋙ RefinementStage.forget := sorry

end toTargetDiagram

end SeparatingStage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
