/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.LocalizedChern.Situation
import stacks_project.Chap42.Situation_42_7_1

/- Situation 42.50.1: the setup for a perfect derived module with vanishing or
rank-bounded restriction away from a closed center, under one of four finiteness hypotheses. -/
@[stacks 0GUJ] #check
  (@AlgebraicGeometry.LocalizedChern.Situation :
    (S : AlgebraicGeometry.Scheme) →
      [AlgebraicGeometry.UniversallyCatenary S] →
      (δ : S → ℤ) →
      [IsDimensionFunction δ] →
      (X : CategoryTheory.Over S) →
      [AlgebraicGeometry.LocallyOfFiniteType X.hom] →
      {Z : AlgebraicGeometry.Scheme} →
      (i : Z ⟶ X.left) →
      [AlgebraicGeometry.IsClosedImmersion i] →
      X.left.toRingedSpace.ModuleDerived →
      ℕ → AlgebraicGeometry.LocalizedChern.RestrictionBehavior → Prop)
