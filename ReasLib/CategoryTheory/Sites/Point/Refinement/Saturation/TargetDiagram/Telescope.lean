module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.Telescope.Basic

/-!
# Telescopes of directed target diagrams

This leaf owns the source-free telescope target of a directed diagram of
finite-cover targets, its component inclusions, and request transport into the
telescope.  Completion consequences are kept in `TargetDiagram.Completion`.
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

/-- Support data for the telescope of a source-free target-refinement diagram.  The
telescope index may live in a larger universe than each component index. -/
structure TelescopeTarget (D : κ ⥤ Target.{u, v, q, r'} C) where
  /-- Essential smallness of the telescope index in the fiber universe. -/
  indexEssentiallySmall : EssentiallySmall.{q} (toPreorder D).telescope.indexᵒᵖ
  /-- Colimits in the presheaf fiber of the telescope system. -/
  presheafFiberHasColimits :
    letI : EssentiallySmall.{q} (toPreorder D).telescope.indexᵒᵖ := indexEssentiallySmall
    HasColimitsOfShape
      (EssentiallySmallFiber.fiber (toPreorder D).telescope.diagram).Elementsᵒᵖ (Type q)

namespace TelescopeTarget

variable {D : κ ⥤ Target.{u, v, q, r'} C}

/-- Source-free telescope support packages are unique because all their fields are propositions. -/
instance instSubsingleton : Subsingleton (TelescopeTarget D) := sorry

/-- Ambient smallness and fiber-colimit instances provide source-free telescope support. -/
noncomputable def of (D : κ ⥤ Target.{u, v, q, r'} C)
    [EssentiallySmall.{q} (toPreorder D).telescope.indexᵒᵖ]
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber (toPreorder D).telescope.diagram).Elementsᵒᵖ (Type q)] :
    TelescopeTarget D where
  indexEssentiallySmall := inferInstance
  presheafFiberHasColimits := inferInstance

/-- Package source-free telescope support as the ordinary target owner. -/
noncomputable def toTarget (T : TelescopeTarget D) :
    Target.{u, v, q, max z r'} C where
  system := (toPreorder D).telescope
  indexEssentiallySmall := T.indexEssentiallySmall
  presheafFiberHasColimits := T.presheafFiberHasColimits

namespace toTarget

/-- The system carried by a telescope target is the canonical telescope system. -/
@[simp]
theorem system (T : TelescopeTarget D) :
    T.toTarget.system = (toPreorder D).telescope := sorry

/-- The diagram carried by a telescope target is the canonical telescope diagram. -/
@[simp]
theorem diagram (T : TelescopeTarget D) :
    T.toTarget.diagram = (toPreorder D).telescope.diagram := sorry

end toTarget

end TelescopeTarget

/-- The canonical source-free refinement from a diagram component to its telescope target. -/
noncomputable def telescopeInclusion (D : κ ⥤ Target.{u, v, q, r'} C)
    (target : TelescopeTarget D) (a : κ) :
    Target.Hom (stage D a) target.toTarget where
  refinement := DirectedPreorderSystem.StageDiagram.Telescope.refinement (toPreorder D) a

namespace telescopeInclusion

/-- The ordered refinement underlying a target telescope inclusion is the canonical telescope
refinement from that diagram component. -/
@[simp]
theorem toRefinement (D : κ ⥤ Target.{u, v, q, r'} C)
    (target : TelescopeTarget D) (a : κ) :
    (telescopeInclusion D target a).toRefinement =
      DirectedPreorderSystem.StageDiagram.Telescope.refinement (toPreorder D) a := sorry

/-- Telescope inclusions form a cocone over the original target diagram. -/
@[simp]
theorem naturality (D : κ ⥤ Target.{u, v, q, r'} C)
    (target : TelescopeTarget D) {a b : κ} (hab : a ≤ b) :
    Target.Hom.comp (hom D hab) (telescopeInclusion D target b) =
      telescopeInclusion D target a := sorry

end telescopeInclusion

/-- Transport a component request to the telescope through its named target refinement.  The
packaged source and telescope targets supply all required smallness instances. -/
noncomputable def telescopeMapRequest (D : κ ⥤ Target.{u, v, q, r'} C)
    (target : TelescopeTarget D) (a : κ) (request : (stage D a).Request J) :
    target.toTarget.Request J :=
  Target.Hom.mapRequest (telescopeInclusion D target a) request

namespace telescopeMapRequest

/-- A request realized at one target-diagram component remains realized after transport to the
telescope target. -/
theorem isRealized (D : κ ⥤ Target.{u, v, q, r'} C)
    (target : TelescopeTarget D) (a : κ) (request : (stage D a).Request J)
    (h_request : request.is_realized) :
    (telescopeMapRequest D target a request).is_realized := sorry

end telescopeMapRequest

namespace telescopeInclusion

/-- Request transport through a telescope inclusion is the target-morphism request transport. -/
@[simp]
theorem mapRequest (D : κ ⥤ Target.{u, v, q, r'} C)
    (target : TelescopeTarget D) (a : κ) (request : (stage D a).Request J) :
    (telescopeInclusion D target a).mapRequest request =
      telescopeMapRequest D target a request := sorry

namespace mapRequest

/-- Request transport through telescope inclusions is natural in the component index. -/
theorem naturality (D : κ ⥤ Target.{u, v, q, r'} C)
    (target : TelescopeTarget D) {a b : κ} (hab : a ≤ b)
    (request : (stage D a).Request J) :
    telescopeMapRequest D target a request =
      telescopeMapRequest D target b ((hom D hab).mapRequest request) := sorry

end mapRequest

end telescopeInclusion

end Target.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
