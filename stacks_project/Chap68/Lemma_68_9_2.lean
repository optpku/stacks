/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Integral scheme covers of quasi-compact quasi-separated algebraic spaces

A quasi-compact quasi-separated algebraic space admits a surjective integral
morphism from a scheme, which may be chosen to factor Zariski-locally through
any given surjective étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : Y ⟶ X` Zariski-locally factors through `u : U ⟶ X` if every
point of `Y` has an open neighbourhood on which `f` factors through `u`. -/
def zariskiLocallyFactorsThrough {S : Scheme.{u}} {Y X U : AlgebraicSpace S}
    (f : Y ⟶ X) (u : U ⟶ X) : Prop :=
  ∀ y : Points Y, ∃ V : OpenSubspace Y,
    y ∈ V.pointsSet ∧ ∃ g : V.X ⟶ U, V.ι ≫ f = g ≫ u

/-- Unfolding of `zariskiLocallyFactorsThrough`. -/
theorem zariskiLocallyFactorsThrough_iff {S : Scheme.{u}}
    {Y X U : AlgebraicSpace S} (f : Y ⟶ X) (u : U ⟶ X) :
    zariskiLocallyFactorsThrough f u ↔
      ∀ y : Points Y, ∃ V : OpenSubspace Y,
        y ∈ V.pointsSet ∧ ∃ g : V.X ⟶ U, V.ι ≫ f = g ≫ u :=
  sorry

/-- Lemma 68.9.2 (1): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. There exists a surjective integral
morphism `Y ⟶ X` where `Y` is a scheme. -/
@[stacks 09YB]
theorem exists_surjective_isIntegralHom_isScheme {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f :=
  sorry

/-- Lemma 68.9.2 (2): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Given a surjective étale morphism
`U ⟶ X` we may choose a surjective integral morphism `Y ⟶ X` with `Y` a scheme
such that for every `y ∈ Y` there is an open neighbourhood `V ⊂ Y` such that
`V ⟶ X` factors through `U`. -/
@[stacks 09YB]
theorem exists_surjective_isIntegralHom_isScheme_locallyFactorsThrough
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {U : AlgebraicSpace S} (u : U ⟶ X) [Surjective u] [Etale u] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f ∧
        zariskiLocallyFactorsThrough f u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
