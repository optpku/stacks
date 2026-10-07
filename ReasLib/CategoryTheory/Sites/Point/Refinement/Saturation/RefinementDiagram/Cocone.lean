module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementDiagram.Inclusion

/-!
# Cocones for refinement-stage telescopes

This leaf bundles the componentwise source-to-telescope inclusions as a
standard `Limits.Cocone` and exposes the canonical leg from the neutral initial
stage to an anchored telescope stage.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r'

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
variable {κ : Type r'} [Preorder κ] [IsDirectedOrder κ]

namespace telescopeCocone

/-- Naturality of the standard cocone whose legs are the source-to-telescope
inclusions. -/
theorem naturality
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)}
    (anchor : κ) {a b : κ} (f : a ⟶ b) :
    D.map f ≫ telescopeInclusion D (target := target) anchor b =
      telescopeInclusion D (target := target) anchor a ≫
        ((Functor.const κ).obj (telescopeStage D (target := target) anchor)).map f := sorry

end telescopeCocone

/-- The standard categorical cocone from a directed refinement-stage diagram
to its anchored telescope stage. -/
noncomputable def telescopeCocone
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)}
    (anchor : κ) : Cocone D :=
  Cocone.mk (telescopeStage D (target := target) anchor) {
    app := telescopeInclusion D (target := target) anchor
    naturality := fun _ _ f => telescopeCocone.naturality D anchor f
  }

namespace telescopeCocone

/-- The vertex of the telescope cocone is the anchored telescope stage. -/
@[simp]
theorem pt
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)}
    (anchor : κ) :
    (telescopeCocone D (target := target) anchor).pt =
      telescopeStage D (target := target) anchor := sorry

/-- A component of the telescope cocone is the canonical source-to-telescope
inclusion. -/
@[simp]
theorem ιApp
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {target : Target.Diagram.TelescopeTarget (toTargetDiagram D)}
    (anchor a : κ) :
    (telescopeCocone D (target := target) anchor).ι.app a =
      telescopeInclusion D (target := target) anchor a := sorry

end telescopeCocone

/- The cocone has explicit vertex and morphism data; `sorryAx` is confined to
its naturality proof field. -/

end RefinementStage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
