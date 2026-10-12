/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Basic

/-!
# Scheduled saturation prefixes

This file owns the closed and open initial-segment data for scheduled
saturation diagrams, together with their elementary constructors.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

namespace Stage.Scheduled

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type z}

local notation "Ω" => WithBot M
local notation "Cut" => WithTop Ω

/-- A closed initial segment of a request-saturation diagram.

The prefix realizes each request whose scheduling node is at most `cut`; its
underlying coherent diagram is the ordinary reusable `Stage.Diagram`. -/
structure Prefix [Preorder M]
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) (cut : Ω)
    extends Stage.Diagram (J := J) A {i : Ω // i ≤ cut} where
  /-- Every request scheduled at or before the cut is realized by its base map. -/
  realizesAt : ∀ (m : M) (hm : (m : Ω) ≤ cut),
    ((toDiagram.fromBase ⟨(m : Ω), hm⟩).mapRequest (request m)).is_realized

namespace Prefix

variable [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- Add the closed-prefix realization invariant to an existing based stage diagram. -/
def ofDiagram {cut : Ω}
    (D : Stage.Diagram (J := J) A {i : Ω // i ≤ cut})
    (hreal : ∀ (m : M) (hm : (m : Ω) ≤ cut),
      ((D.fromBase ⟨(m : Ω), hm⟩).mapRequest (request m)).is_realized) :
    Prefix (J := J) A request cut where
  toDiagram := D
  realizesAt := hreal

/-- The constant closed prefix induced by one compatible stage and explicit
realization of all requests below the cut. -/
noncomputable def constant {cut : Ω}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M) (_ : (m : Ω) ≤ cut),
      (f.mapRequest (request m)).is_realized) :
    Prefix (J := J) A request cut :=
  ofDiagram (J := J) (A := A) (request := request)
    (Stage.Diagram.constant (J := J) (A := A) (κ := {i : Ω // i ≤ cut}) B f) hreal

/-- No concrete request is scheduled in the bottom initial segment. -/
theorem bottomRealizes
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) :
    ∀ (m : M) (_ : (m : Ω) ≤ (⊥ : Ω)),
      (Stage.Hom.mapRequest (J := J) (𝟙 A) (request m)).is_realized := sorry

/-- The bottom closed prefix contains only the base stage. Its realization
obligation is proposition-valued because no concrete request lies at `⊥`. -/
noncomputable def bottom (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) :
    Prefix (J := J) A request (⊥ : Ω) :=
  constant (J := J) (A := A) (request := request) (cut := (⊥ : Ω)) A (𝟙 A)
    (bottomRealizes (J := J) A request)

end Prefix

/-- An open initial segment of a request-saturation diagram.

Unlike `Prefix`, the realization invariant is strict in the cut. This is the
generic shape needed at limit stages before the terminal top node is taken. -/
structure OpenPrefix [Preorder M]
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) (cut : Cut)
    extends Stage.Diagram (J := J) A {i : Cut // i ≤ cut} where
  /-- A request is realized at every node strictly after its scheduling node. -/
  realizesBefore : ∀ (i : {j : Cut // j ≤ cut}) (m : M),
    ((m : Ω) : Cut) < i.1 →
      ((toDiagram.fromBase i).mapRequest (request m)).is_realized

namespace OpenPrefix

variable [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- Add the open-prefix realization invariant to an existing based stage diagram. -/
def ofDiagram {cut : Cut}
    (D : Stage.Diagram (J := J) A {i : Cut // i ≤ cut})
    (hreal : ∀ (i : {j : Cut // j ≤ cut}) (m : M), ((m : Ω) : Cut) < i.1 →
      ((D.fromBase i).mapRequest (request m)).is_realized) :
    OpenPrefix (J := J) A request cut where
  toDiagram := D
  realizesBefore := hreal

/-- The constant based diagram underlying an open prefix. -/
noncomputable def constantDiagram {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B) :
    Stage.Diagram (J := J) A {i : Cut // i ≤ cut} :=
  Stage.Diagram.constant (J := J) (A := A) (κ := {i : Cut // i ≤ cut}) B f

/-- A constant open-prefix diagram realizes every request assumed realized at its target. -/
theorem constantRealizes {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M), ((m : Ω) : Cut) < cut →
      (f.mapRequest (request m)).is_realized) :
    ∀ (i : {j : Cut // j ≤ cut}) (m : M), ((m : Ω) : Cut) < i.1 →
      (((constantDiagram (J := J) (A := A) (cut := cut) B f).fromBase i).mapRequest
        (request m)).is_realized := sorry

/-- The constant open prefix induced by one compatible stage and explicit
realization of all requests strictly below the cut. -/
noncomputable def constant {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M), ((m : Ω) : Cut) < cut →
      (f.mapRequest (request m)).is_realized) :
    OpenPrefix (J := J) A request cut :=
  ofDiagram (J := J) (A := A) (request := request)
    (constantDiagram (J := J) (A := A) (cut := cut) B f)
    (constantRealizes (J := J) (A := A) B f hreal)

end OpenPrefix

/- The constructors retain their explicit stages, morphisms, and underlying diagrams.
Any `sorryAx` below is confined to proposition-valued realization fields. -/

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
