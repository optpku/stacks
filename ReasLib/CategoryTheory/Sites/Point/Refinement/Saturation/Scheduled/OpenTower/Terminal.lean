/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.OpenTower.Operations

/-!
# Terminal computations for open scheduled saturation towers
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

/-- The terminal adapter selects the tower stage at the adjoined top cut. -/
@[simp]
theorem toTerminal.stage (T : Stage.Scheduled.OpenTower (J := J) A request) :
    T.toTerminal.stage = T.toDiagram.stage (⊤ : Cut) := sorry

/-- The terminal adapter selects the tower base leg at the adjoined top cut. -/
@[simp]
theorem toTerminal.hom (T : Stage.Scheduled.OpenTower (J := J) A request) :
    T.toTerminal.hom = T.toDiagram.fromBase (⊤ : Cut) := sorry

/-- Evaluating a tower directly at top agrees with first restricting it to
the terminal top prefix. -/
@[simp]
theorem toTerminal.eqTopPrefix
    (T : Stage.Scheduled.OpenTower (J := J) A request) :
    T.toTerminal = T.toTopPrefix.toTerminal := sorry

/-- The scheduled diagram obtained from an open tower is constant at its top
stage. -/
@[simp]
theorem toTerminalDiagram.toDiagram
    (T : Stage.Scheduled.OpenTower (J := J) A request) :
    T.toTerminalDiagram.toDiagram =
      Stage.Diagram.constant (J := J) (A := A) (κ := Ω)
        (T.toDiagram.stage (⊤ : Cut)) (T.toDiagram.fromBase (⊤ : Cut)) := sorry

/-- Every stage of the scheduled adapter is the top stage of the tower. -/
@[simp]
theorem toTerminalDiagram.stage
    (T : Stage.Scheduled.OpenTower (J := J) A request) (i : Ω) :
    T.toTerminalDiagram.toDiagram.stage i = T.toDiagram.stage (⊤ : Cut) := sorry

/-- Every transition of the scheduled adapter is the identity of the tower's
top stage. -/
@[simp]
theorem toTerminalDiagram.hom
    (T : Stage.Scheduled.OpenTower (J := J) A request)
    {i j : Ω} (hij : i ≤ j) :
    T.toTerminalDiagram.toDiagram.hom hij = 𝟙 (T.toDiagram.stage (⊤ : Cut)) := sorry

/-- Every base leg of the scheduled adapter is the tower base leg at top. -/
@[simp]
theorem toTerminalDiagram.fromBase
    (T : Stage.Scheduled.OpenTower (J := J) A request) (i : Ω) :
    T.toTerminalDiagram.toDiagram.fromBase i =
      T.toDiagram.fromBase (⊤ : Cut) := sorry

end OpenTower

namespace Terminal

namespace toOpenTower

/-- Every stage of the open tower associated to terminal data is its terminal
stage. -/
@[simp]
theorem stage (T : Stage.Scheduled.Terminal (J := J) A request)
    (cut : Cut) :
    T.toOpenTower.toDiagram.stage cut = T.stage := sorry

/-- Every transition in the open tower associated to terminal data is an
identity. -/
@[simp]
theorem hom (T : Stage.Scheduled.Terminal (J := J) A request)
    {cut cut' : Cut} (hcut : cut ≤ cut') :
    T.toOpenTower.toDiagram.hom hcut = 𝟙 T.stage := sorry

/-- Every base leg in the open tower associated to terminal data is its
terminal morphism. -/
@[simp]
theorem fromBase (T : Stage.Scheduled.Terminal (J := J) A request)
    (cut : Cut) :
    T.toOpenTower.toDiagram.fromBase cut = T.hom := sorry

/-- Evaluating the constant open tower associated to terminal data recovers
that terminal data. -/
@[simp]
theorem toTerminal (T : Stage.Scheduled.Terminal (J := J) A request) :
    T.toOpenTower.toTerminal = T := sorry

/-- Collapsing the constant open tower associated to terminal data recovers
the canonical constant scheduled diagram. -/
@[simp]
theorem toTerminalDiagram
    (T : Stage.Scheduled.Terminal (J := J) A request) :
    T.toOpenTower.toTerminalDiagram =
      Stage.Scheduled.Diagram.ofTerminal (J := J) T := sorry

end toOpenTower

end Terminal

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
