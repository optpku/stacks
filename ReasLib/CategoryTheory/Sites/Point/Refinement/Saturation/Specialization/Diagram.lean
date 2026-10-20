/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.SeparatingDiagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Stage
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Category
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Diagram.Basic

/-!
# Diagram Specialization Bridges

This leaf forgets a based diagram of scheduled saturation stages to the ordinary neutral
refinement-stage and finite-cover target diagrams used by the telescope API.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

namespace Stage.Diagram

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {κ : Type z} [Preorder κ]

/-- Forget solved-request scheduling from every component of a based saturation-stage diagram
while retaining its separating data. -/
noncomputable def toSeparatingDiagram (D : Diagram (J := J) A κ) :
    κ ⥤ SeparatingStage.{u, v, q, r, r'} S P x y :=
  D.functor ⋙ Stage.forgetSolved

namespace toSeparatingDiagram

/-- A component of the scheduling-forgetful diagram is the separating stage underlying the
corresponding scheduled stage. -/
@[simp]
theorem obj (D : Diagram (J := J) A κ) (i : κ) :
    D.toSeparatingDiagram.obj i = (D.stage i).toSeparatingStage := sorry

/-- A transition of the scheduling-forgetful diagram is the separating-stage morphism underlying
the corresponding scheduled-stage transition. -/
@[simp]
theorem map (D : Diagram (J := J) A κ)
    {i j : κ} (hij : i ≤ j) :
    D.toSeparatingDiagram.map (homOfLE hij) = (D.hom hij).toSeparatingStage := sorry

end toSeparatingDiagram

/-- Forget the separating pair and solved-request data from every component of a based
saturation-stage diagram.  The construction factors through the separating-stage diagram. -/
noncomputable def toRefinementDiagram (D : Diagram (J := J) A κ) :
    κ ⥤ RefinementStage.{u, v, q, r, r'} S :=
  SeparatingStage.Diagram.toRefinementDiagram D.toSeparatingDiagram

namespace toRefinementDiagram

/-- The generic component of a forgotten saturation-stage diagram is the forgotten component
stage. -/
@[simp]
theorem obj (D : Diagram (J := J) A κ) (i : κ) :
    D.toRefinementDiagram.obj i = (D.stage i).toRefinementStage := sorry

/-- The generic transition of a forgotten saturation-stage diagram is the forgotten transition
morphism. -/
@[simp]
theorem map (D : Diagram (J := J) A κ)
    {i j : κ} (hij : i ≤ j) :
    D.toRefinementDiagram.map (homOfLE hij) = (D.hom hij).toRefinementStage := sorry

/-- Forgetting a scheduled diagram to refinement stages factors through the intermediate diagram
of separating stages. -/
theorem factorization (D : Diagram (J := J) A κ) :
    D.toRefinementDiagram =
      SeparatingStage.Diagram.toRefinementDiagram D.toSeparatingDiagram := sorry

end toRefinementDiagram

/-- Forget a based saturation-stage diagram directly to its neutral diagram of finite-cover
targets.  This factors through the generic refinement-stage diagram rather than rebuilding the
target functor. -/
noncomputable def toTargetDiagram (D : Diagram (J := J) A κ) :
    κ ⥤ Target.{u, v, q, r'} C :=
  SeparatingStage.Diagram.toTargetDiagram D.toSeparatingDiagram

namespace toTargetDiagram

/-- The target component of a forgotten saturation-stage diagram is the target of the original
stage. -/
@[simp]
theorem obj (D : Diagram (J := J) A κ) (i : κ) :
    D.toTargetDiagram.obj i = (D.stage i).target := sorry

/-- A transition in the neutral target diagram is the fully forgotten saturation-stage
transition. -/
@[simp]
theorem map (D : Diagram (J := J) A κ)
    {i j : κ} (hij : i ≤ j) :
    D.toTargetDiagram.map (homOfLE hij) =
      (D.hom hij).toRefinementStage.toTarget := sorry

/-- Forgetting a saturation-stage transition to the neutral target diagram retains its ordered
refinement. -/
@[simp]
theorem map.toRefinement (D : Diagram (J := J) A κ)
    {i j : κ} (hij : i ≤ j) :
    (D.toTargetDiagram.map (homOfLE hij)).toRefinement = (D.hom hij).toRefinement := sorry

/-- Forgetting a scheduled diagram to targets factors through its diagram of separating stages. -/
theorem factorization (D : Diagram (J := J) A κ) :
    D.toTargetDiagram =
      SeparatingStage.Diagram.toTargetDiagram D.toSeparatingDiagram := sorry

/-- Forgetting a scheduled diagram to targets also factors through its neutral
refinement-stage diagram. -/
theorem throughRefinement (D : Diagram (J := J) A κ) :
    D.toTargetDiagram = D.toRefinementDiagram ⋙ RefinementStage.forget := sorry

end toTargetDiagram

end Stage.Diagram

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
