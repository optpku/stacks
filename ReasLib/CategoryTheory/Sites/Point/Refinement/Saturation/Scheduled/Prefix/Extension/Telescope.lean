/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit.Cocone
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Predecessor

/-!
# Telescope extensions at scheduling cuts

This leaf turns a telescope cocone on the strict-predecessor diagram into the
neutral `CutExtension` datum.  The cofinality hypothesis says exactly that
each scheduled request below the cut occurs strictly before some predecessor.

The index type lives in the target-index universe because the homogeneous
stage telescope API requires this universe agreement.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix

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

namespace Predecessor

/-- Every index below `cut` lies below a strict predecessor when `Set.Iio cut`
has no greatest element. -/
theorem existsAbove [NoMaxOrder (Set.Iio cut)]
    (i : WithTop (WithBot M)) (hi : i < cut) :
    ∃ j : Set.Iio cut, i < j.1 := sorry

end Predecessor

variable {D : Stage.Diagram (J := J) A (Set.Iio cut)}
variable [IsDirectedOrder (Set.Iio cut)]

namespace baseToTelescope

/-- The base-to-telescope morphism realizes every request below the cut when
the predecessor diagram realizes earlier requests and the predecessors are
strictly cofinal below the cut. -/
theorem realizesBefore
    (hD : PredecessorRealizes (request := request) D)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ((D.baseToTelescope anchor).mapRequest (request m)).is_realized := sorry

end baseToTelescope

namespace CutExtension

/-- Build a cut extension from the canonical telescope cocone, an explicit
strict-predecessor realization invariant, and cofinality below the cut. -/
noncomputable def ofTelescope
    (hD : PredecessorRealizes (request := request) D)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    CutExtension (request := request) D where
  cocone := D.underTelescopeCocone anchor
  realizesBefore := baseToTelescope.realizesBefore hD hcofinal anchor

namespace ofTelescope

/-- Build the telescope cut extension when strict predecessors have no
greatest element. -/
noncomputable def ofNoMax [NoMaxOrder (Set.Iio cut)]
    (hD : PredecessorRealizes (request := request) D)
    {target : Target.Diagram.TelescopeTarget D.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) D target) :
    CutExtension (request := request) D :=
  CutExtension.ofTelescope hD (fun m hm =>
    Predecessor.existsAbove ((m : WithBot M) : WithTop (WithBot M)) hm) anchor

end ofTelescope
end CutExtension

/- The telescope cocone, all component legs, and the base map are explicit.
`sorryAx` is confined to realization and computation propositions. -/

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
