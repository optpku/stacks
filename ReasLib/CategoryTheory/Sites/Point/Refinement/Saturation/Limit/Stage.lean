/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Diagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementDiagram.Telescope
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Completion

/-!
# Telescope stages of saturation diagrams

This leaf turns the neutral telescope of a directed target diagram into a
scheduled separating stage.  It owns the separation anchor, transported solved
set, and resulting stage, but not the component inclusions into that stage.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r'

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
variable {κ : Type r'} [Preorder κ] [IsDirectedOrder κ]

/-- A separation witness at a diagram index after passing to the telescope refinement. -/
def telescopeSeparates (D : Diagram (J := J) A κ)
    (target : Target.Diagram.TelescopeTarget D.toTargetDiagram) (a : κ) : Prop :=
  OrderedRefinement.EssentiallySmall.Separates
    (RefinementStage.Diagram.telescopeRefinement D.toRefinementDiagram target a) P x y

/-- A chosen diagram index whose telescope refinement still separates the two fixed source
fiber elements. -/
structure TelescopeAnchor (D : Diagram (J := J) A κ)
    (target : Target.Diagram.TelescopeTarget D.toTargetDiagram) where
  /-- The selected base index. -/
  index : κ
  /-- Separation after transporting from the selected base leg into the telescope. -/
  separates : D.telescopeSeparates target index

/-- Telescope anchors with the same selected diagram index are equal. -/
@[ext]
theorem TelescopeAnchor.ext {D : Diagram (J := J) A κ}
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    {a b : TelescopeAnchor (J := J) D target} (hindex : a.index = b.index) :
    a = b := sorry

/-- The solved-request set on a telescope is the union of the solved requests of its diagram
stages, transported along their canonical telescope refinements. -/
noncomputable def telescopeSolved (D : Diagram (J := J) A κ)
    (target : Target.Diagram.TelescopeTarget D.toTargetDiagram) :
    Set (target.toTarget.Request J) :=
  {request | ∃ a : κ,
      ∃ sourceRequest : (D.stage a).toSeparatingStage.target.Request J,
        sourceRequest ∈ (D.stage a).solved ∧
          Target.Diagram.telescopeMapRequest D.toTargetDiagram target a sourceRequest = request}

namespace telescopeSolved

/-- Membership in the telescope solved set is witnessed by a solved request from one diagram
component and its canonical telescope transport. -/
@[simp]
theorem mem_iff (D : Diagram (J := J) A κ)
    (target : Target.Diagram.TelescopeTarget D.toTargetDiagram)
    (request : target.toTarget.Request J) :
    request ∈ D.telescopeSolved target ↔
      ∃ a : κ, ∃ sourceRequest : (D.stage a).toSeparatingStage.target.Request J,
        sourceRequest ∈ (D.stage a).solved ∧
          Target.Diagram.telescopeMapRequest D.toTargetDiagram target a sourceRequest =
            request := sorry

/-- Every request in the transported telescope solved set is realized in the telescope target. -/
theorem realized (D : Diagram (J := J) A κ)
    (target : Target.Diagram.TelescopeTarget D.toTargetDiagram)
    {request : target.toTarget.Request J}
    (h_request : request ∈ D.telescopeSolved target) :
    request.is_realized := sorry

end telescopeSolved

/-- The scheduled separating refinement stage carried by the telescope of a coherent
diagram.  Its concrete target system and solved set are determined by the diagram; only
smallness/colimit support and a separation anchor are supplied externally. -/
noncomputable def telescopeStage (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    Stage.{u, v, q, r, r'} (J := J) S P x y where
  toSeparatingStage := {
    target := target.toTarget
    refinement :=
      RefinementStage.Diagram.telescopeRefinement D.toRefinementDiagram target anchor.index
    separates := anchor.separates
  }
  solved := D.telescopeSolved target
  solvedRealized := fun {request} h_request =>
    telescopeSolved.realized D target (request := request) h_request

namespace telescopeStage

/-- The target of a telescope limit stage is the neutral target-diagram telescope. -/
@[simp]
theorem target (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    (D.telescopeStage anchor).target = target.toTarget := sorry

/-- The source refinement of a telescope limit stage is owned by the generic refinement-diagram
telescope. -/
@[simp]
theorem toRefinement (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    (D.telescopeStage anchor).toRefinement =
      RefinementStage.Diagram.telescopeRefinement D.toRefinementDiagram target anchor.index := sorry

/-- The solved set recorded by a telescope limit stage is the transported solved set of its
underlying diagram. -/
@[simp]
theorem solved (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    (D.telescopeStage anchor).solved = D.telescopeSolved target := sorry

/-- Telescope limit stages are independent of the chosen separation anchor. -/
theorem eq (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (a b : TelescopeAnchor (J := J) D target) :
    D.telescopeStage a = D.telescopeStage b := sorry

/-- If every component request is eventually realized in a directed stage diagram, the telescope
stage realizes every request on its target fiber. -/
theorem targetComplete (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target)
    (h_eventual : Target.Diagram.eventuallyRealizes (J := J) D.toTargetDiagram) :
    (D.telescopeStage anchor).targetComplete := sorry

end telescopeStage

/- Data and axiom audit (mathlib 4.32): target support and request transport are owned by
`Target.Diagram`; this leaf explicitly adds the solved set and separating stage.  Any `sorryAx`
below is confined to proof-law, realization, separation, or solved-set fields. -/

end Stage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
