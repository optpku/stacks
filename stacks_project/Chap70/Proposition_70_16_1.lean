/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap68.Lemma_68_9_2

/-!
# Finite scheme covers of quasi-compact quasi-separated algebraic spaces

A quasi-compact quasi-separated algebraic space admits a surjective finite
morphism of finite presentation from a scheme, which may be chosen to factor
Zariski-locally through any given surjective étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proposition 70.16.1 (1): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. There exists a surjective finite
morphism `Y ⟶ X` of finite presentation where `Y` is a scheme. -/
@[stacks 09YC]
theorem exists_surjective_isFinite_finitePresentation_isScheme
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f :=
  sorry

/-- Proposition 70.16.1 (2): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Given a surjective étale morphism
`U ⟶ X` we may choose a surjective finite morphism `Y ⟶ X` of finite
presentation with `Y` a scheme such that for every `y ∈ Y` there is an open
neighbourhood `V ⊂ Y` such that `V ⟶ X` factors through `U`. -/
@[stacks 09YC]
theorem exists_surjective_isFinite_finitePresentation_isScheme_locallyFactorsThrough
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {U : AlgebraicSpace S} (u : U ⟶ X) [Surjective u] [Etale u] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f ∧
        zariskiLocallyFactorsThrough f u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
