/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Construction

/-!
# Reduced induced structures and reduction of algebraic spaces

Every closed subset of the points of an algebraic space has a canonical reduced induced
structure, obtained from the unique reduced closed subspace with that point-set. The reduction
of an algebraic space is that structure on the whole space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The reduced induced algebraic space structure on a closed subset of `Points X`. -/
def reduced (Z : Closeds (Points X)) : ClosedSubspaceStructure Z :=
  ofSubspace (ReducedClosed.Immersion.closedSubspace X Z)
    (ReducedClosed.Immersion.pointsSet_eq X Z)

/-- The reduced induced structure on `Z` is a reduced closed subspace with point-set `Z`. -/
theorem reduced_spec (Z : Closeds (Points X)) :
    (reduced Z).subspace.pointsSet = Z.carrier ∧
      hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
        (reduced Z).space :=
  sorry

/-- A reduced algebraic space structure on `Z` admits a unique morphism over `X` to the reduced
induced structure. -/
theorem reduced_unique {Z : Closeds (Points X)} (T : ClosedSubspaceStructure Z)
    (hT : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) T.space) :
    ∃! f : T.space ⟶ (reduced Z).space, f ≫ (reduced Z).ι = T.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The reduction of an algebraic space is the reduced induced structure on its space of
points. -/
def reduction (X : AlgebraicSpace S) : AlgebraicSpace S :=
  (ClosedSubspaceStructure.reduced (⊤ : Closeds (Points X))).space

/-- The canonical closed immersion from the reduction into the original algebraic space. -/
def reductionι (X : AlgebraicSpace S) : reduction X ⟶ X :=
  (ClosedSubspaceStructure.reduced (⊤ : Closeds (Points X))).ι

/-- The reduction of `X` is reduced, its inclusion is a closed immersion, and that inclusion is
surjective on points. -/
theorem reduction_spec (X : AlgebraicSpace S) :
    hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) (reduction X) ∧
      IsClosedImmersion (reductionι X) ∧
      Function.Surjective (Points.map (reductionι X)) :=
  sorry

/-- The reduction of `X` is the underlying space of the reduced induced structure on `⊤`. -/
theorem reduction_eq_reduced_top (X : AlgebraicSpace S) :
    reduction X = (ClosedSubspaceStructure.reduced (⊤ : Closeds (Points X))).space :=
  sorry

/-- The reduction inclusion is the inclusion of the reduced induced structure on `⊤`. -/
theorem reductionι_eq_reduced_top_ι (X : AlgebraicSpace S) :
    reductionι X = (ClosedSubspaceStructure.reduced (⊤ : Closeds (Points X))).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
