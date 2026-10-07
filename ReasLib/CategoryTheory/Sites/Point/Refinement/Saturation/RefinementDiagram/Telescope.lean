module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementDiagram.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Telescope

/-!
# Telescope stages of refinement-stage diagrams

This leaf adds the data that depends on the fixed source inverse system: the
source-to-telescope refinement selected through one component, and the
resulting anchored refinement stage.  Component inclusions are kept in the
next leaf.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace RefinementStage.Diagram

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {κ : Type z} [Preorder κ] [IsDirectedOrder κ]

/-- The refinement from the fixed original system to a telescope target, selected through one
explicit component.  The component is needed here because this construction records a concrete
source factorization. -/
noncomputable def telescopeRefinement (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    (target : Target.Diagram.TelescopeTarget (toTargetDiagram D)) (anchor : κ) :
    OrderedRefinement S target.toTarget.diagram :=
  (stage D anchor).toRefinement.comp
    (Target.Diagram.telescopeInclusion (toTargetDiagram D) target anchor).toRefinement

namespace telescopeRefinement

/-- Choosing a later comparable component gives the same source-to-telescope refinement. -/
theorem eqOfLE
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    (target : Target.Diagram.TelescopeTarget (toTargetDiagram D))
    {a b : κ} (hab : a ≤ b) :
    telescopeRefinement D target a = telescopeRefinement D target b := sorry

/-- The source-to-telescope refinement is independent of the chosen component in a directed
diagram. -/
theorem eq (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    (target : Target.Diagram.TelescopeTarget (toTargetDiagram D)) (a b : κ) :
    telescopeRefinement D target a = telescopeRefinement D target b := sorry

end telescopeRefinement

/-- The refinement stage carried by a source-refinement bridge into a target telescope.  Its
anchor is explicit because it determines the source-to-telescope refinement. -/
noncomputable def telescopeStage (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (anchor : κ) :
    RefinementStage.{u, v, q, r, max z r'} S where
  target := target.toTarget
  refinement := telescopeRefinement D target anchor

namespace telescopeStage

/-- The target of an anchored source telescope stage is the source-free telescope target. -/
@[simp]
theorem target (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (anchor : κ) :
    (telescopeStage D (target := target) anchor).target = target.toTarget := sorry

/-- The refinement carried by a source telescope stage is the selected source-to-telescope
refinement. -/
@[simp]
theorem toRefinement (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (anchor : κ) :
    (telescopeStage D (target := target) anchor).toRefinement =
      telescopeRefinement D target anchor := sorry

/-- Anchored source telescope stages are independent of the chosen component. -/
theorem eq (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (a b : κ) :
    telescopeStage D (target := target) a = telescopeStage D (target := target) b := sorry

end telescopeStage

end RefinementStage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
