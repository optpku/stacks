module

public import stacks_project.Chap83.Definition_83_5_13_SetTheoretic

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/-- Lemma 83.5.16 (1): if a pre-relation `j : R ⟶ U ⨯ U` over `B` is a pre-equivalence
relation, then it is a set-theoretic pre-equivalence relation. This holds in particular
when `j` comes from a groupoid in algebraic spaces, or from an action of a group
algebraic space on `U`. -/
@[stacks 0492]
theorem isSetTheoreticPreEquivalence_of_isPreEquivalence (P : PreRelation U)
    (hP : P.IsPreEquivalence) : P.IsSetTheoreticPreEquivalence :=
  sorry

/-- Lemma 83.5.16 (2): if a pre-relation `j : R ⟶ U ⨯ U` over `B` is an equivalence
relation, then it is a set-theoretic equivalence relation. -/
@[stacks 0492]
instance isSetTheoreticEquivalence_of_isEquivalenceRelation (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] : P.IsSetTheoreticEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
