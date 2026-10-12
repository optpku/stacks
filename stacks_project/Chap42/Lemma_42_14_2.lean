/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.CycleGroup.Localization
import stacks_project.Chap42.Situation_42_7_1

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 42.14.2: for an open subscheme `U ⊆ X` and its reduced closed complement,
the sequence of relative degree-`k` cycle groups given by closed pushforward and open pullback
is exact and ends surjectively at the cycle group of `U`. -/
@[stacks 02RC] #check
  (AlgebraicGeometry.CycleGroup.Localization.exact :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
      [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
      (U : X.Opens) (k : ℤ),
      (AlgebraicGeometry.CycleGroup.Localization.complex p δ U k).Exact ∧
        Epi (AlgebraicGeometry.CycleGroup.Localization.complex p δ U k).g)
