/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Diagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementTower.Diagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Tower.Diagram

/-!
# Saturation-tower specialization

This leaf forgets separation and solved-request scheduling from a sequential
saturation tower.  It exposes compatibility with the neutral refinement-stage
and target diagrams so downstream completion arguments can change layer
without rebuilding a tower.
-/

@[expose] public section

open CategoryTheory Limits Opposite

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

namespace forget

/-- Forgetting a saturation-tower step preserves its all-request realization
property. -/
theorem realizes
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S) (P := P) (x := x) (y := y))
    (n : ℕ) :
    ((T.step n).toRefinementStage).realizesAll (J := J) := sorry

end forget

/-- Forget separation and solved-request scheduling from every stage and step
of a sequential saturation tower. -/
noncomputable def forget
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S) (P := P) (x := x) (y := y)) :
    RefinementStage.Tower.{u, v, q, r, r'} (J := J) (S := S) where
  stage := fun n => (T.stage n).toRefinementStage
  step := fun n => (T.step n).toRefinementStage
  realizes := forget.realizes T

namespace forget

/-- Forgetting a tower retains each stage through the stage-level forgetful
map. -/
@[simp]
theorem stage
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S) (P := P) (x := x) (y := y))
    (n : ℕ) :
    T.forget.stage n = (T.stage n).toRefinementStage := sorry

/-- Forgetting a tower retains each successor map through the morphism-level
forgetful map. -/
@[simp]
theorem step
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S) (P := P) (x := x) (y := y))
    (n : ℕ) :
    T.forget.step n = (T.step n).toRefinementStage := sorry

/-- The natural-number diagram of a forgotten tower is obtained by applying
the stage forgetful functor to the original natural-number diagram. -/
theorem natDiagram
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S) (P := P) (x := x) (y := y)) :
    T.forget.natDiagram =
      T.natDiagram ⋙ Stage.forget (J := J) (S := S) (P := P) (x := x) (y := y) := sorry

/-- Forgetting a derived tower comparison agrees with deriving the comparison
after forgetting the tower. -/
@[simp]
theorem hom
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S) (P := P) (x := x) (y := y))
    {n m : ℕ} (hnm : n ≤ m) :
    T.forget.hom hnm = (T.hom hnm).toRefinementStage := sorry

/-- The lifted diagram of a forgotten tower is the refinement-stage diagram
obtained by forgetting the original based tower diagram. -/
theorem toDiagram
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S) (P := P) (x := x) (y := y)) :
    T.forget.toDiagram = T.toDiagram.toRefinementDiagram := sorry

/-- Passing a forgotten tower to target diagrams agrees with forgetting the
original based tower diagram directly to targets. -/
theorem toTargetDiagram
    (T : Tower.{u, v, q, r, r'} (J := J) (S := S) (P := P) (x := x) (y := y)) :
    RefinementStage.Diagram.toTargetDiagram T.forget.toDiagram =
      T.toDiagram.toTargetDiagram := sorry

end forget

/- The forgotten tower's stage and step data are explicit projections.  Any
`sorryAx` dependency is confined to proposition-valued realization and
functor-coherence fields inherited from the two tower owners. -/

end Tower
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
