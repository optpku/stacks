/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.DenseOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.11.4: a flat proper morphism that is finite over a dense open is finite
if the morphism is locally of finite presentation or the open is retrocompact. -/
@[stacks 0B48] #check
  (AlgebraicGeometry.IsFinite.of_restrict_of_flat :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      [AlgebraicGeometry.Flat f] →
      [AlgebraicGeometry.IsProper f] →
      (U : S.Opens) →
      Dense (U : Set S) →
      [AlgebraicGeometry.IsFinite (f ∣_ U)] →
      (AlgebraicGeometry.LocallyOfFinitePresentation f ∨
        IsRetrocompact (U : Set S)) →
      AlgebraicGeometry.IsFinite f)
