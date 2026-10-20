/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.EtaleRelation

/-!
# Algebraization of an étale equivalence relation from the open complement and the completion

A pair of morphisms of algebraic spaces over a locally Noetherian algebraic
space `X` that is an étale equivalence relation off a closed subset `T` and an
equivalence relation with étale projections after completion along `T` is an
étale equivalence relation over `X`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Lemma 88.25.6: Let `S` be a scheme. Let `X` be a locally Noetherian algebraic
space over `S`. Let `T ⊂ Points X` be a closed subset. Let `s, t : R ⟶ U` be two
morphisms of algebraic spaces over `X`. Assume `R`, `U` are locally of finite type
over `X`, the base change of `s` and `t` to `X \ T` is an étale equivalence
relation, and the formal completion `(t_/T, s_/T)` is an equivalence relation too.
Then `(t, s)` is an étale equivalence relation on `U` over `X`.

The base change of `s` and `t` to `X \ T` is
`(overPullback (openComplementι X T)).map t` and
`(overPullback (openComplementι X T)).map s`. The completed pair is
`mapOver T t` and `mapOver T s`. The explicit formal étaleness premises for
these completed projections formalize the étaleness used in the proof. -/
@[stacks 0AR8] #check
  (AlgebraicGeometry.AlgebraicSpace.completionAlong.isEtaleEquivalenceRelation :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {R U : Over X} (t s : R ⟶ U)
    [LocallyOfFiniteType R.hom] [LocallyOfFiniteType U.hom]
    [IsEtaleEquivalenceRelation ((overPullback (openComplementι X T)).map t)
      ((overPullback (openComplementι X T)).map s)]
    [IsEquivalenceRelation (completionAlong.mapOver T t) (completionAlong.mapOver T s)]
    [AlgebraicGeometry.FormalAlgebraicSpace.Etale (completionAlong.mapOver T t)]
    [AlgebraicGeometry.FormalAlgebraicSpace.Etale (completionAlong.mapOver T s)],
    IsEtaleEquivalenceRelation t s)
