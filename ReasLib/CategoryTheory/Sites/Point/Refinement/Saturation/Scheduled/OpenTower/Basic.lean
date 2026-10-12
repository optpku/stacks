/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Basic

/-!
# Open scheduled saturation towers

An open tower is a coherent based diagram over all cuts of
`WithTop (WithBot M)`.  Its realization invariant is strict in the cut, so the
adjoined top realizes every concrete scheduled request.
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

local notation "Ω" => WithBot M
local notation "Cut" => WithTop Ω

/-- A coherent open tower of scheduled saturation stages over all
cuts.  Request `m` is realized at every cut strictly after its scheduling
index. -/
structure OpenTower
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J)
    extends Stage.Diagram (J := J) A Cut where
  /-- Every request is realized at each cut strictly after its schedule. -/
  realizesBefore : ∀ (cut : Cut) (m : M), ((m : Ω) : Cut) < cut →
    ((toDiagram.fromBase cut).mapRequest (request m)).is_realized

namespace OpenTower

variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- Add the open-tower realization invariant to a coherent based diagram. -/
def ofDiagram (D : Stage.Diagram (J := J) A Cut)
    (hreal : ∀ (cut : Cut) (m : M), ((m : Ω) : Cut) < cut →
      ((D.fromBase cut).mapRequest (request m)).is_realized) :
    OpenTower (J := J) A request where
  toDiagram := D
  realizesBefore := hreal

/-- A constant tower realizes every scheduled request when its chosen base
leg already realizes every request. -/
theorem constant.realizes
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized) :
    ∀ (cut : Cut) (m : M), ((m : Ω) : Cut) < cut →
      (((Stage.Diagram.constant (J := J) (A := A) (κ := Cut) B f).fromBase cut).mapRequest
        (request m)).is_realized := sorry

/-- The constant open tower induced by one compatible stage that realizes
every scheduled request. -/
noncomputable def constant
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized) :
    OpenTower (J := J) A request :=
  ofDiagram (J := J) (A := A) (request := request)
    (Stage.Diagram.constant (J := J) (A := A) (κ := Cut) B f)
    (constant.realizes B f hreal)

end OpenTower

/- The constructors retain their explicit diagram, stage, and base map.  Any
`sorryAx` dependency below is confined to proposition-valued coherence or
realization fields. -/

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
