module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Basic

/-!
# Realization on strict-predecessor diagrams

This leaf owns the realization invariant for a based stage diagram indexed by
all strict predecessors of a scheduling cut.  It is independent of any gluing
construction.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

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
variable {M : Type z} [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}
variable {cut : WithTop (WithBot M)}

/-- The open-prefix realization invariant on a based diagram indexed by all
strict predecessors of a cut. -/
def PredecessorRealizes
    (D : Stage.Diagram (J := J) A
      {i : WithTop (WithBot M) // i < cut}) : Prop :=
  ∀ (i : {j : WithTop (WithBot M) // j < cut}) (m : M),
    ((m : WithBot M) : WithTop (WithBot M)) < i.1 →
    ((D.fromBase i).mapRequest (request m)).is_realized

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
