module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementTower.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementDiagram.Telescope
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Completion

/-!
# Diagrams and telescope completion of refinement towers

This leaf exposes the ordinary directed diagram of an unseparated sequential
tower and the completion consequences of its successor realization property.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace RefinementStage
namespace Tower

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]

section DiagramImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The transition assigned to an identity in the lifted tower index is an identity. -/
private theorem mapId
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S)) (n : Index) :
    T.hom ((ULift.down_le).mpr (leOfHom (𝟙 n))) = 𝟙 (T.stage n.down) := sorry

/-- Derived transitions respect composition in the lifted tower index. -/
private theorem mapComp
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S))
    {n m p : Index} (f : n ⟶ m) (g : m ⟶ p) :
    T.hom ((ULift.down_le).mpr (leOfHom (f ≫ g))) =
      T.hom ((ULift.down_le).mpr (leOfHom f)) ≫
        T.hom ((ULift.down_le).mpr (leOfHom g)) := sorry

end Implementation

/-- View an unseparated tower as an ordinary directed diagram of refinement stages. -/
noncomputable def toDiagram (T : Tower.{u, v, q, r, r'} (J := J) (S := S)) :
    Index ⥤ RefinementStage.{u, v, q, r, r'} S where
  obj := fun n => T.stage n.down
  map := fun hnm => T.hom ((ULift.down_le).mpr (leOfHom hnm))
  map_id := Implementation.mapId T
  map_comp := Implementation.mapComp T

end DiagramImplementation

namespace toDiagram

/-- The diagram component at a lifted index is the corresponding tower stage. -/
@[simp]
theorem stage (T : Tower.{u, v, q, r, r'} (J := J) (S := S)) (n : Index) :
    T.toDiagram.obj n = T.stage n.down := sorry

/-- The diagram transition is the corresponding derived tower refinement. -/
@[simp]
theorem hom (T : Tower.{u, v, q, r, r'} (J := J) (S := S))
    {n m : Index} (hnm : n ≤ m) :
    T.toDiagram.map (homOfLE hnm) = T.hom ((ULift.down_le).mpr hnm) := sorry

end toDiagram

/-- Successor realization supplies eventual realization for the tower's target diagram. -/
theorem eventuallyRealizes (T : Tower.{u, v, q, r, r'} (J := J) (S := S)) :
    Target.Diagram.eventuallyRealizes (J := J)
      (RefinementStage.Diagram.toTargetDiagram T.toDiagram) := sorry

/-- The target telescope of an unseparated tower is finite-cover complete. -/
theorem telescopeTargetComplete
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S))
    {target : Target.Diagram.TelescopeTarget
      (RefinementStage.Diagram.toTargetDiagram T.toDiagram)} :
    target.toTarget.complete J := sorry

namespace telescopeStage

/-- An anchored source-refinement telescope stage has the complete telescope target. -/
theorem targetComplete
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S))
    {target : Target.Diagram.TelescopeTarget
      (RefinementStage.Diagram.toTargetDiagram T.toDiagram)} (anchor : Index) :
    (RefinementStage.Diagram.telescopeStage T.toDiagram
      (target := target) anchor).target.complete J := sorry

end telescopeStage

end Tower
end RefinementStage
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
