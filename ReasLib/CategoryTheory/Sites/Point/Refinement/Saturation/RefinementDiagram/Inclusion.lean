/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementDiagram.Telescope

/-!
# Inclusions into refinement-stage telescopes

This leaf owns the factorized component maps into an anchored telescope stage,
including their target, refinement, request-transport, and naturality API.
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
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {κ : Type z} [Preorder κ] [IsDirectedOrder κ]

namespace telescopeInclusion

/-- The target telescope inclusion factors the source refinement through the anchored
source-to-telescope refinement. -/
theorem factorization
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (anchor a : κ) :
    IsFactorization (stage D a).toRefinement
      (Target.Diagram.telescopeInclusion (toTargetDiagram D) target a).toRefinement
      (telescopeStage D (target := target) anchor).toRefinement := sorry

end telescopeInclusion

/-- The canonical factorized refinement from a diagram component to an anchored source telescope
stage.  Its target-side ordered refinement is owned by `Target.Diagram.telescopeInclusion`. -/
noncomputable def telescopeInclusion (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (anchor a : κ) :
    RefinementStage.Hom (stage D a) (telescopeStage D (target := target) anchor) where
  refinement :=
    (Target.Diagram.telescopeInclusion (toTargetDiagram D) target a).toRefinement
  factorization := telescopeInclusion.factorization D anchor a

namespace telescopeInclusion

/-- Forgetting the source factorization from a source telescope inclusion gives the canonical
target telescope inclusion. -/
@[simp]
theorem toTarget
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (anchor a : κ) :
    (telescopeInclusion D (target := target) anchor a).toTarget =
      Target.Diagram.telescopeInclusion (toTargetDiagram D) target a := sorry

/-- The ordered refinement underlying a source telescope inclusion is the source-free target
telescope inclusion. -/
@[simp]
theorem toRefinement (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (anchor a : κ) :
    (telescopeInclusion D (target := target) anchor a).toRefinement =
      (Target.Diagram.telescopeInclusion (toTargetDiagram D) target a).toRefinement := sorry

/-- Source telescope inclusions form a cocone over the refinement-stage diagram. -/
@[simp]
theorem naturality
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)}
    (anchor : κ) {a b : κ} (hab : a ≤ b) :
    RefinementStage.Hom.comp (hom D hab)
        (telescopeInclusion D (target := target) anchor b) =
      telescopeInclusion D (target := target) anchor a := sorry

/-- Request transport along a source telescope inclusion is the canonical request transport of
the underlying source-free target inclusion. -/
@[simp]
theorem mapRequest (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)} (anchor a : κ)
    (request : (stage D a).target.Request J) :
    (telescopeInclusion D (target := target) anchor a).mapRequest request =
      Target.Diagram.telescopeMapRequest (toTargetDiagram D) target a request := sorry

namespace mapRequest

/-- Request transport through source telescope inclusions is natural in the component index. -/
theorem naturality
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)}
    (anchor : κ) {a b : κ} (hab : a ≤ b)
    (request : (stage D a).target.Request J) :
    (telescopeInclusion D (target := target) anchor a).mapRequest request =
      (telescopeInclusion D (target := target) anchor b).mapRequest
        ((hom D hab).mapRequest request) := sorry

end mapRequest

end telescopeInclusion

/- The concrete refinement of `telescopeInclusion` is explicit; `sorryAx` is
confined to its proposition-valued factorization law. -/

end RefinementStage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
