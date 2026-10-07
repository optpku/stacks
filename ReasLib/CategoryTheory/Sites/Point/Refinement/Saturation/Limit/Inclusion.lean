module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit.Stage

/-!
# Component inclusions into saturation telescope stages

This leaf owns the canonical stage morphisms from the components of a directed
saturation diagram to its telescope stage, together with their factorization,
solved-set, computation, and naturality API.
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

namespace telescopeInclusion

/-- The target telescope refinement makes each component refinement factor through the anchored
source-to-telescope refinement. -/
theorem factorization (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) (a : κ) :
    IsFactorization (D.stage a).toRefinement
      (Target.Diagram.telescopeInclusion D.toTargetDiagram target a).toRefinement
      (D.telescopeStage anchor).toRefinement := sorry

/-- Transport to the telescope carries every solved component request into the telescope solved
set. -/
theorem solvedMono (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) (a : κ) :
    ∀ ⦃request : (D.stage a).toSeparatingStage.target.Request J⦄,
      request ∈ (D.stage a).solved →
        Target.Diagram.telescopeMapRequest D.toTargetDiagram target a request ∈
          (D.telescopeStage anchor).solved := sorry

end telescopeInclusion

/-- The canonical stage morphism from a diagram component to its telescope limit stage. -/
noncomputable def telescopeInclusion (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target)
    (a : κ) :
    D.stage a ⟶ D.telescopeStage anchor where
  toSeparatingStage := {
    refinement := (Target.Diagram.telescopeInclusion D.toTargetDiagram target a).toRefinement
    factorization := telescopeInclusion.factorization D anchor a
  }
  solvedMono := telescopeInclusion.solvedMono D anchor a

namespace telescopeInclusion

/-- The ordered refinement underlying a telescope inclusion is the canonical refinement from
the corresponding diagram stage into its telescope system. -/
@[simp]
theorem toRefinement (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target)
    (a : κ) :
    (D.telescopeInclusion anchor a).toRefinement =
      (Target.Diagram.telescopeInclusion D.toTargetDiagram target a).toRefinement := sorry

/-- Telescope inclusions form a cocone over the scheduled-stage diagram. -/
@[simp]
theorem naturality (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target)
    {a b : κ} (hab : a ≤ b) :
    Stage.Hom.comp (D.hom hab) (D.telescopeInclusion anchor b) =
      D.telescopeInclusion anchor a := sorry

/-- Request transport along a telescope inclusion is the named component-to-telescope transport
provided by this limit API. -/
@[simp]
theorem mapRequest (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) (a : κ)
    (request : (D.stage a).toSeparatingStage.target.Request J) :
    (D.telescopeInclusion anchor a).mapRequest request =
      Target.Diagram.telescopeMapRequest D.toTargetDiagram target a request := sorry

namespace mapRequest

/-- Request transport through scheduled-stage telescope inclusions is natural in the component
index. -/
theorem naturality (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target)
    {a b : κ} (hab : a ≤ b)
    (request : (D.stage a).toSeparatingStage.target.Request J) :
    (D.telescopeInclusion anchor a).mapRequest request =
      (D.telescopeInclusion anchor b).mapRequest ((D.hom hab).mapRequest request) := sorry

end mapRequest

end telescopeInclusion

/- The concrete telescope inclusion is explicit; `sorryAx` is confined to its factorization,
solved-set, computation, and naturality propositions. -/

end Stage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
