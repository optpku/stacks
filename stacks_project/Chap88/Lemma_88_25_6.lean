/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_19_1_BaseChange
public import stacks_project.Chap88.«88_27_0_1_Completion»
public import stacks_project.Chap88.Lemma_88_25_6_EtaleRelation

/-!
# Algebraization of an étale equivalence relation from the open complement and the completion

A pair of morphisms of algebraic spaces over a locally Noetherian algebraic
space `X` that is an étale equivalence relation off a closed subset `T` and an
equivalence relation after completion along `T` is an étale equivalence
relation over `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

set_option synthInstance.checkSynthOrder false in
/-- Lemma 88.25.6: Let `S` be a scheme. Let `X` be a locally Noetherian algebraic
space over `S`. Let `T ⊂ Points X` be a closed subset. Let `s, t : R ⟶ U` be two
morphisms of algebraic spaces over `X`. Assume `R`, `U` are locally of finite type
over `X`, the base change of `s` and `t` to `X \ T` is an étale equivalence
relation, and the formal completion `(t_/T, s_/T)` is an equivalence relation too.
Then `(t, s)` is an étale equivalence relation on `U` over `X`.

The base change of `s` and `t` to `X \ T` is
`(overPullback (openComplementι X T)).map t` and
`(overPullback (openComplementι X T)).map s`. The completed pair is
`mapOver T t` and `mapOver T s`. -/
@[stacks 0AR8, instance]
instance isEtaleEquivalenceRelation {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {R U : Over X} (t s : R ⟶ U)
    [LocallyOfFiniteType R.hom] [LocallyOfFiniteType U.hom]
    [IsEtaleEquivalenceRelation ((overPullback (openComplementι X T)).map t)
      ((overPullback (openComplementι X T)).map s)]
    [IsEquivalenceRelation (mapOver T t) (mapOver T s)] :
    IsEtaleEquivalenceRelation t s :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
