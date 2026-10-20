module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Telescope

/-!
# Computations for telescope cut extensions

This file exposes the based cocone, stage, predecessor-leg, and base-leg
formulas for telescope cut extensions, including the canonical no-maximum
constructor.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix.CutExtension.ofTelescope

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type r'} [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}
variable {cut : WithTop (WithBot M)}
variable {D : Stage.Diagram (J := J) A (Set.Iio cut)}
variable [IsDirectedOrder (Set.Iio cut)]

namespace ofNoMax

/-- The no-maximum telescope extension retains the canonical based telescope
cocone. -/
@[simp]
theorem cocone [NoMaxOrder (Set.Iio cut)]
    (hD : PredecessorRealizes (request := request) D)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    (ofTelescope.ofNoMax hD anchor).cocone =
      D.underTelescopeCocone anchor := sorry

/-- The no-maximum telescope extension carries the telescope stage. -/
@[simp]
theorem stage [NoMaxOrder (Set.Iio cut)]
    (hD : PredecessorRealizes (request := request) D)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    (ofTelescope.ofNoMax hD anchor).stage =
      D.telescopeStage anchor := sorry

/-- A leg of the no-maximum telescope extension is its telescope inclusion. -/
@[simp]
theorem leg [NoMaxOrder (Set.Iio cut)]
    (hD : PredecessorRealizes (request := request) D)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target)
    (i : Set.Iio cut) :
    (ofTelescope.ofNoMax hD anchor).leg i =
      D.telescopeInclusion anchor i := sorry

/-- The base leg of the no-maximum telescope extension is the canonical
base-to-telescope morphism. -/
@[simp]
theorem fromBase [NoMaxOrder (Set.Iio cut)]
    (hD : PredecessorRealizes (request := request) D)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    (ofTelescope.ofNoMax hD anchor).fromBase =
      D.baseToTelescope anchor := sorry

end ofNoMax

/-- The cocone of a telescope cut extension is the canonical based telescope
cocone in `Under A`. -/
@[simp]
theorem cocone
    (hD : PredecessorRealizes (request := request) D)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    (CutExtension.ofTelescope hD hcofinal anchor).cocone =
      D.underTelescopeCocone anchor := sorry

/-- The stage of a telescope cut extension is the telescope stage. -/
@[simp]
theorem stage
    (hD : PredecessorRealizes (request := request) D)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    (CutExtension.ofTelescope hD hcofinal anchor).stage =
      D.telescopeStage anchor := sorry

/-- A leg of a telescope cut extension is the corresponding telescope
inclusion. -/
@[simp]
theorem leg
    (hD : PredecessorRealizes (request := request) D)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target)
    (i : Set.Iio cut) :
    (CutExtension.ofTelescope hD hcofinal anchor).leg i =
      D.telescopeInclusion anchor i := sorry

/-- The base leg of a telescope cut extension is the canonical
base-to-telescope morphism. -/
@[simp]
theorem fromBase
    (hD : PredecessorRealizes (request := request) D)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    (CutExtension.ofTelescope hD hcofinal anchor).fromBase =
      D.baseToTelescope anchor := sorry

end Stage.Scheduled.OpenPrefix.CutExtension.ofTelescope
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
