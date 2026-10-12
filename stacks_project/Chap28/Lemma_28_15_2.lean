/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Unibranch.Normal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.15.2: a normal scheme is geometrically unibranch. -/
@[stacks 0BQ3] #check
  (AlgebraicGeometry.Scheme.isGeometricallyUnibranch_of_isNormal :
    ∀ {X : AlgebraicGeometry.Scheme.{u}},
      X.isNormal → X.isGeometricallyUnibranch)
