module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Operations

/-!
# Adapters between scheduled diagrams and closed prefixes

This file restricts a global scheduled diagram to a closed initial segment.
Together with `Prefix.toScheduledDiagram`, it gives the two directions of the
canonical reindexing at a greatest cut.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled

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

local notation "Ω" => WithBot M

namespace Diagram

/-- Forget the bound carried by an index of a closed initial segment. -/
def prefixIndex (cut : Ω) : {i : Ω // i ≤ cut} →o Ω :=
  OrderHom.Subtype.val (· ≤ cut)

/-- Restrict the coherent diagram underlying a scheduled diagram to the
closed initial segment ending at `cut`. -/
noncomputable def prefixDiagram (D : Stage.Scheduled.Diagram (J := J) A request)
    (cut : Ω) : Stage.Diagram (J := J) A {i : Ω // i ≤ cut} :=
  Stage.Diagram.reindex (J := J) D.toDiagram (prefixIndex cut)

/-- The restricted diagram realizes every request scheduled in its closed
initial segment. -/
theorem prefixRealizes (D : Stage.Scheduled.Diagram (J := J) A request)
    (cut : Ω) :
    ∀ (m : M) (hm : (m : Ω) ≤ cut),
      (Stage.Hom.mapRequest (J := J)
        ((D.prefixDiagram cut).fromBase ⟨(m : Ω), hm⟩) (request m)).is_realized := sorry

/-- Restrict a global scheduled diagram to the closed prefix ending at
`cut`. -/
noncomputable def toPrefix (D : Stage.Scheduled.Diagram (J := J) A request)
    (cut : Ω) : Stage.Scheduled.Prefix (J := J) A request cut :=
  Prefix.ofDiagram (J := J) (A := A) (request := request)
    (D.prefixDiagram cut) (D.prefixRealizes cut)

end Diagram

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
