/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 65.10.1: the restriction of an étale equivalence relation along an étale morphism is
again an étale equivalence relation. -/
@[stacks 02WT] #check
  (@AlgebraicGeometry.Scheme.PreRelation.instIsEtaleEquivalenceRelationPullback :
    ∀ {S : Scheme.{u}} {U U' : Over S} (P : Scheme.PreRelation U) (g : U' ⟶ U)
      [P.IsEtaleEquivalenceRelation] [Etale g.left],
        (P.pullback g).IsEtaleEquivalenceRelation)
