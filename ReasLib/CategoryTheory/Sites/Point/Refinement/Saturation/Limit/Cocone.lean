/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit.Inclusion

/-!
# Based cocones for saturation-stage telescopes

This leaf packages the component inclusions of a telescope stage as a standard
cocone, constructs the canonical leg from the based diagram's source, and
records its factorization through every component.  It also exposes the same
data as a cocone in `Under A`.
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

namespace telescopeCocone

/-- Naturality of the standard cocone whose legs are the canonical stage
telescope inclusions. -/
theorem naturality (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) {a b : κ} (f : a ⟶ b) :
    D.functor.map f ≫ D.telescopeInclusion anchor b =
      D.telescopeInclusion anchor a ≫
        ((Functor.const κ).obj (D.telescopeStage anchor)).map f := sorry

end telescopeCocone

/-- The standard categorical cocone from a based stage diagram to its
telescope stage. -/
noncomputable def telescopeCocone (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) : Cocone D.functor :=
  Cocone.mk (D.telescopeStage anchor) {
    app := D.telescopeInclusion anchor
    naturality := fun _ _ f => telescopeCocone.naturality D anchor f
  }

namespace telescopeCocone

/-- The vertex of the stage telescope cocone is its telescope stage. -/
@[simp]
theorem pt (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    (D.telescopeCocone anchor).pt = D.telescopeStage anchor := sorry

/-- A component of the stage telescope cocone is the canonical telescope
inclusion at that index. -/
@[simp]
theorem ιApp (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) (a : κ) :
    (D.telescopeCocone anchor).ι.app a = D.telescopeInclusion anchor a := sorry

end telescopeCocone

/-- The canonical morphism from the base stage of a based diagram to its
telescope stage. -/
noncomputable def baseToTelescope (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    A ⟶ D.telescopeStage anchor :=
  D.fromBase anchor.index ≫ D.telescopeInclusion anchor anchor.index

namespace baseToTelescope

/-- The base-to-telescope morphism factors through every diagram component and
the corresponding telescope cocone leg. -/
theorem fac (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) (a : κ) :
    D.baseToTelescope anchor =
      D.fromBase a ≫ (D.telescopeCocone anchor).ι.app a := sorry

/-- The ordered refinement underlying the base-to-telescope morphism is the
composite through the anchor component. -/
@[simp]
theorem toRefinement (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    (D.baseToTelescope anchor).toRefinement =
      (D.fromBase anchor.index).toRefinement.comp
        (D.telescopeInclusion anchor anchor.index).toRefinement := sorry

/-- Request transport along the base-to-telescope morphism may be computed
through any diagram component. -/
theorem mapRequest (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) (a : κ)
    (request : A.target.Request J) :
    (D.baseToTelescope anchor).mapRequest request =
      (D.telescopeInclusion anchor a).mapRequest
        ((D.fromBase a).mapRequest request) := sorry

end baseToTelescope

/-- The based telescope cocone regarded as a cocone in `Under A`. -/
noncomputable def underTelescopeCocone (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    Cocone (Under.lift D.functor D.base) :=
  Under.liftCocone D.functor D.base (D.telescopeCocone anchor)
    (D.baseToTelescope anchor) (fun a => (baseToTelescope.fac D anchor a).symm)

namespace underTelescopeCocone

/-- The object underlying the point of the lifted telescope cocone is the
telescope stage. -/
@[simp]
theorem ptRight (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    (D.underTelescopeCocone anchor).pt.right = D.telescopeStage anchor := sorry

/-- The structure map of the lifted telescope point is the canonical
base-to-telescope morphism. -/
@[simp]
theorem ptHom (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) :
    (D.underTelescopeCocone anchor).pt.hom = D.baseToTelescope anchor := sorry

/-- Forgetting a lifted telescope leg gives the corresponding stage telescope
inclusion. -/
@[simp]
theorem ιAppRight (D : Diagram (J := J) A κ)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : TelescopeAnchor (J := J) D target) (a : κ) :
    ((D.underTelescopeCocone anchor).ι.app a).right =
      D.telescopeInclusion anchor a := sorry

end underTelescopeCocone

/- The cocones and their morphism data are explicit; `sorryAx` is confined to
naturality, factorization, and computation propositions. -/

end Stage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
