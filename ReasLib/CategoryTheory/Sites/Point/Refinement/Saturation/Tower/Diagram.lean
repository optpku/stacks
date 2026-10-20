/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Tower.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit.Stage

/-!
# Diagrams and telescope completion of saturation towers

This leaf exposes the canonical based diagram of a sequential saturation
tower and the completion consequences of its successor realization property.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Tower

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

section DiagramImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The comparison assigned to an identity of lifted tower indices is the identity. -/
private theorem mapId
    (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y)) (n : Index) :
    T.hom ((ULift.down_le).mpr (leOfHom (𝟙 n))) = 𝟙 (T.stage n.down) := sorry

/-- Comparisons assigned to composable lifted-index morphisms preserve composition. -/
private theorem mapComp
    (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y))
    {n m p : Index} (f : n ⟶ m) (g : m ⟶ p) :
    T.hom ((ULift.down_le).mpr (leOfHom (f ≫ g))) =
      T.hom ((ULift.down_le).mpr (leOfHom f)) ≫
        T.hom ((ULift.down_le).mpr (leOfHom g)) := sorry

/-- Comparisons from level zero are natural with respect to lifted tower transitions. -/
private theorem baseNaturality
    (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y))
    {n m : Index} (f : n ⟶ m) :
    ((Functor.const Index).obj (T.stage 0)).map f ≫ T.hom (Nat.zero_le m.down) =
      T.hom (Nat.zero_le n.down) ≫
        T.hom ((ULift.down_le).mpr (leOfHom f)) := sorry

end Implementation

/-- View a sequential saturation tower as the canonical based diagram of its stages. -/
noncomputable def toDiagram
    (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y)) :
    Stage.Diagram (J := J) (T.stage 0) Index where
  functor := {
    obj := fun n => T.stage n.down
    map := fun hnm => T.hom ((ULift.down_le).mpr (leOfHom hnm))
    map_id := Implementation.mapId T
    map_comp := Implementation.mapComp T
  }
  base := {
    app := fun n => T.hom (Nat.zero_le n.down)
    naturality := fun _ _ f => Implementation.baseNaturality T f
  }

end DiagramImplementation

namespace toDiagram

/-- The stage at a tower-diagram index is the corresponding tower stage. -/
@[simp]
theorem stage (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y))
    (n : Index) :
    T.toDiagram.stage n = T.stage n.down := sorry

/-- The base map in the tower diagram is the derived comparison out of level zero. -/
@[simp]
theorem fromBase (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y))
    (n : Index) :
    T.toDiagram.fromBase n = T.hom (Nat.zero_le n.down) := sorry

/-- The transition in a tower's diagram is the corresponding derived tower comparison. -/
@[simp]
theorem hom (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y))
    {n m : Index} (hnm : n ≤ m) :
    T.toDiagram.hom hnm = T.hom ((ULift.down_le).mpr hnm) := sorry

end toDiagram

/-- The successor realization property of a tower supplies eventual realization for the
target diagram underlying its canonical based diagram. -/
theorem eventuallyRealizes (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y)) :
    Target.Diagram.eventuallyRealizes (J := J) T.toDiagram.toTargetDiagram := sorry

/-- The telescope target of a sequential saturation tower is finite-cover complete. -/
theorem telescopeTargetComplete
    (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y))
    {target : Target.Diagram.TelescopeTarget T.toDiagram.toTargetDiagram} :
    target.toTarget.complete J := sorry

namespace telescopeStage

/-- An anchored telescope stage of a sequential saturation tower is target-complete. -/
theorem targetComplete
    (T : Tower (J := J) (S := S) (P := P) (x := x) (y := y))
    {target : Target.Diagram.TelescopeTarget T.toDiagram.toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) T.toDiagram target) :
    (T.toDiagram.telescopeStage anchor).targetComplete := sorry

end telescopeStage

end Tower
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
