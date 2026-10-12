/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Groupoid
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 78.11.3: with B an algebraic space over a scheme S as in Section 78.3, an
equivalence relation j : R ⟶ U ⨯ U over B extends uniquely to a groupoid in algebraic
spaces (U, R, s, t, c) over B with the same objects, arrows, source, and target. -/
@[stacks 043Y] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.existsUniqueGroupoid :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
        {U : Over B}
        (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U) [IsEquivalenceRelation P.t P.s],
      ∃! G : AlgebraicGeometry.GroupoidAlgebraicSpace B, P.IsGroupoidExtension G)
