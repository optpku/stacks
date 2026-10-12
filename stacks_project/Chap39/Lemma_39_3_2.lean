/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 39.3.2 (1): the pullback of a pre-relation along `g : U' ⟶ U` is a
pre-relation on `U'`. -/
@[stacks 02V8] #check (@AlgebraicGeometry.Scheme.PreRelation.pullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S},
    AlgebraicGeometry.Scheme.PreRelation U → (U' ⟶ U) →
      AlgebraicGeometry.Scheme.PreRelation U')

/- Lemma 39.3.2 (2): pullback preserves the relation condition. -/
@[stacks 02V8] #check (@AlgebraicGeometry.Scheme.PreRelation.instMonoHomPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S}
    (P : AlgebraicGeometry.Scheme.PreRelation U) (g : U' ⟶ U) [Mono P.hom],
      Mono (P.pullback g).hom)

/- Lemma 39.3.2 (3): pullback preserves pre-equivalence relations. -/
@[stacks 02V8] #check
  (@AlgebraicGeometry.Scheme.PreRelation.IsPreEquivalence.pullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S}
      {P : AlgebraicGeometry.Scheme.PreRelation U},
        P.IsPreEquivalence → (g : U' ⟶ U) → (P.pullback g).IsPreEquivalence)

/- Lemma 39.3.2 (4): pullback preserves internal equivalence relations. -/
@[stacks 02V8] #check
  (@AlgebraicGeometry.Scheme.PreRelation.instIsEquivalenceRelationPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S}
      (P : AlgebraicGeometry.Scheme.PreRelation U) (g : U' ⟶ U)
      [IsEquivalenceRelation P.t P.s],
        IsEquivalenceRelation (P.pullback g).t (P.pullback g).s)
