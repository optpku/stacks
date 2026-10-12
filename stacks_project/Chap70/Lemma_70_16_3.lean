/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap68.Lemma_68_9_3

/-!
# Finite scheme covers finite étale over a dense open

A quasi-compact quasi-separated algebraic space whose points space has finitely
many irreducible components admits a surjective finite morphism of finite
presentation from a scheme that is finite étale over a quasi-compact dense open.
Given a surjective étale cover, the morphism may be chosen to factor
Zariski-locally through that cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.16.3 (1): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S` such that `|X|` has finitely many
irreducible components. There exists a surjective finite morphism `Y ⟶ X` of
finite presentation where `Y` is a scheme such that `f` is finite étale over a
quasi-compact dense open `U ⊂ X`. -/
@[stacks 0GUN]
theorem exists_surjective_isFinite_finitePresentation_isScheme_finiteEtaleOver_dense
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (U : OpenSubspace X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f ∧
        IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
          IsFinite (openInverseImageTo f U.ι) ∧
            Etale (openInverseImageTo f U.ι) :=
  sorry

/-- Lemma 70.16.3 (2): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S` such that `|X|` has finitely many
irreducible components. Given a surjective étale morphism `V ⟶ X` we may choose
a surjective finite morphism `Y ⟶ X` of finite presentation with `Y` a scheme,
finite étale over a quasi-compact dense open `U ⊂ X`, such that for every
`y ∈ Y` there is an open neighbourhood `W ⊂ Y` such that `W ⟶ X` factors
through `V`. -/
@[stacks 0GUN]
theorem exists_surjective_isFinite_finitePresentation_isScheme_finiteEtaleOver_dense_locallyFactorsThrough
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X]
    {V : AlgebraicSpace S} (v : V ⟶ X) [Surjective v] [Etale v] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (U : OpenSubspace X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f ∧
        IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
          IsFinite (openInverseImageTo f U.ι) ∧
            Etale (openInverseImageTo f U.ι) ∧
              zariskiLocallyFactorsThrough f v :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
