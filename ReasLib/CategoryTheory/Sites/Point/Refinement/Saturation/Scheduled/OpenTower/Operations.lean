/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.OpenTower.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Operations

/-!
# Operations on open scheduled saturation towers

This file gives both reindexing directions between an open tower and its
terminal top prefix, together with direct terminal and terminal-diagram
adapters.
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
local notation "Cut" => WithTop Ω

namespace OpenTower

/-- Forget the proof that an index lies below the terminal top cut. -/
def topIndex : {i : Cut // i ≤ (⊤ : Cut)} →o Cut :=
  OrderHomClass.toOrderHom
    (OrderIso.IicTop : {i : Cut // i ≤ (⊤ : Cut)} ≃o Cut)

/-- Reindex an open tower over the terminal top initial segment. -/
noncomputable def topPrefixDiagram (T : OpenTower (J := J) A request) :
    Stage.Diagram (J := J) A {i : Cut // i ≤ (⊤ : Cut)} :=
  Stage.Diagram.reindex (J := J) T.toDiagram topIndex

/-- Restricting an open tower to the top initial segment preserves its strict
realization invariant. -/
theorem topPrefixDiagram.realizes (T : OpenTower (J := J) A request) :
    ∀ (i : {j : Cut // j ≤ (⊤ : Cut)}) (m : M), ((m : Ω) : Cut) < i.1 →
      (((T.topPrefixDiagram).fromBase i).mapRequest (request m)).is_realized := sorry

/-- Restrict an open tower to its terminal top prefix. -/
noncomputable def toTopPrefix (T : OpenTower (J := J) A request) :
    OpenPrefix (J := J) A request (⊤ : Cut) :=
  OpenPrefix.ofDiagram (J := J) (A := A) (request := request)
    T.topPrefixDiagram (OpenTower.topPrefixDiagram.realizes T)

/-- The top base leg of an open tower realizes every scheduled request. -/
theorem toTerminal.realizes (T : OpenTower (J := J) A request) :
    ∀ m : M, ((T.toDiagram.fromBase (⊤ : Cut)).mapRequest (request m)).is_realized := sorry

/-- Evaluate an open tower at the terminal top cut to obtain terminal
saturation data. -/
noncomputable def toTerminal (T : OpenTower (J := J) A request) :
    Terminal (J := J) A request where
  stage := T.toDiagram.stage (⊤ : Cut)
  hom := T.toDiagram.fromBase (⊤ : Cut)
  realizes := OpenTower.toTerminal.realizes T

/-- Collapse an open tower to the constant scheduled diagram determined by
its terminal top stage. -/
noncomputable def toTerminalDiagram (T : OpenTower (J := J) A request) :
    Diagram (J := J) A request :=
  Diagram.ofTerminal (J := J) T.toTerminal

end OpenTower

namespace OpenPrefix

/-- Embed every cut into the terminal top prefix. -/
def towerIndex : Cut →o {i : Cut // i ≤ (⊤ : Cut)} :=
  OrderHomClass.toOrderHom
    (OrderIso.IicTop : {i : Cut // i ≤ (⊤ : Cut)} ≃o Cut).symm

/-- Reindex a terminal top prefix over all cuts. -/
noncomputable def towerDiagram
    (D : OpenPrefix (J := J) A request (⊤ : Cut)) :
    Stage.Diagram (J := J) A Cut :=
  Stage.Diagram.reindex (J := J) D.toDiagram towerIndex

/-- Reindexing a terminal top prefix over all cuts preserves its strict
realization invariant. -/
theorem towerDiagram.realizes (D : OpenPrefix (J := J) A request (⊤ : Cut)) :
    ∀ (cut : Cut) (m : M), ((m : Ω) : Cut) < cut →
      (((D.towerDiagram).fromBase cut).mapRequest (request m)).is_realized := sorry

/-- Reindex a terminal top prefix as an open tower over all cuts. -/
noncomputable def toTower (D : OpenPrefix (J := J) A request (⊤ : Cut)) :
    OpenTower (J := J) A request :=
  OpenTower.ofDiagram (J := J) (A := A) (request := request)
    D.towerDiagram (OpenPrefix.towerDiagram.realizes D)

end OpenPrefix

namespace Terminal

/-- Regard terminal saturation data as the constant open tower that it
determines. -/
noncomputable def toOpenTower (T : Terminal (J := J) A request) :
    OpenTower (J := J) A request :=
  OpenTower.constant (J := J) (request := request) T.stage T.hom T.realizes

end Terminal

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
