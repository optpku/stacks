/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Immersion

/-! # Concrete witness for reduced closed-subspace existence -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Construction
variable {S : Scheme.{u}} (X : AlgebraicSpace S) (Z : Closeds (Points X))
/-- Étale-local reducedness of the specified space with its explicit reduced atlas. -/
theorem actual_reduced :
    hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
      (ReducedClosed.Immersion.closedSubspace X Z).X :=
  ⟨ReducedClosed.AtlasImage.reducedAtlas X Z, ReducedClosed.Space.chart X Z,
    ReducedClosed.Space.atlas_etale X Z,
    ReducedClosed.Space.atlas_surjective X Z,
    ReducedClosed.Space.reducedAtlas_reduced X Z⟩

/-- The canonical reduced closed structure is unique over X. This law
does not supply or select any new subspace; the actual candidate is fixed. -/
theorem actual_unique (W : ClosedSubspace X)
    (hs : W.pointsSet = (Z : Set (Points X)))
    (hr : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) W.X) :
    ∃! a : W.X ⟶ (ReducedClosed.Immersion.closedSubspace X Z).X,
      a ≫ (ReducedClosed.Immersion.closedSubspace X Z).ι = W.ι := by
  sorry

/-- Constructive witness of the EXACT proposition consumed by the old owner.
The non-Prop payload is already the actual kernel/image-space construction. -/
theorem exists_reduced :
    ∃ W : ClosedSubspace X,
      W.pointsSet = (Z : Set (Points X)) ∧
        hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) W.X ∧
          ∀ W' : ClosedSubspace X, W'.pointsSet = (Z : Set (Points X)) →
            hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) W'.X →
              ∃! a : W'.X ⟶ W.X, a ≫ W.ι = W'.ι :=
  ⟨ReducedClosed.Immersion.closedSubspace X Z, ReducedClosed.Immersion.pointsSet_eq X Z,
    actual_reduced X Z, actual_unique X Z⟩


end AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Construction
