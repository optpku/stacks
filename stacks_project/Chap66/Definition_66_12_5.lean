/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 66.12.5 (1): an algebraic space structure on a closed subset `Z` of `Points X` is a
closed subspace `Z'` of `X` with `Z'.pointsSet` equal to `Z`. -/
@[stacks 047X] #check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → Closeds (Points X) → Type (u + 1))
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure.ofSubspace :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → {Z : Closeds (Points X)} →
    (W : ClosedSubspace X) → W.pointsSet = Z.carrier → ClosedSubspaceStructure Z)
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure.space :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → {Z : Closeds (Points X)} →
    ClosedSubspaceStructure Z → AlgebraicSpace S)
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure.ι :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → {Z : Closeds (Points X)} →
    (T : ClosedSubspaceStructure Z) → T.space ⟶ X)
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure.spec :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → {Z : Closeds (Points X)} →
    (T : ClosedSubspaceStructure Z) → IsClosedImmersion T.ι ∧ T.subspace.pointsSet = Z.carrier)

/- Definition 66.12.5 (2): the reduced induced algebraic space structure on `Z` is the one
constructed in Lemma 66.12.3. -/
@[stacks 047X] #check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure.reduced :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (Z : Closeds (Points X)) →
    ClosedSubspaceStructure Z)
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure.reduced_spec :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (Z : Closeds (Points X)) →
    (ClosedSubspaceStructure.reduced Z).subspace.pointsSet = Z.carrier ∧
      hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
        (ClosedSubspaceStructure.reduced Z).space)

/- Definition 66.12.5 (3): the reduction `X_red` of `X` is the reduced induced algebraic space
structure on `Points X`. -/
@[stacks 047X] #check (AlgebraicGeometry.AlgebraicSpace.reduction :
  {S : Scheme.{u}} → AlgebraicSpace S → AlgebraicSpace S)
#check (AlgebraicGeometry.AlgebraicSpace.reductionι :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → reduction X ⟶ X)
#check (AlgebraicGeometry.AlgebraicSpace.reduction_spec :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) →
    hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) (reduction X) ∧
      IsClosedImmersion (reductionι X) ∧ Function.Surjective (Points.map (reductionι X)))

end AlgebraicGeometry.AlgebraicSpace
