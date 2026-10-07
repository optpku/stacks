module

public import Mathlib.AlgebraicGeometry.Stalk
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Obtaining a scheme from stalkwise base changes

A quasi-compact quasi-separated algebraic space over a scheme is itself a scheme
once every base change to the spectrum of the stalk of the base at the image of
a point is a scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.17.3: Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism from an algebraic space to a scheme `S`. If for every `x : Points X`
with image `s = f(x)` the algebraic space `X ×_S Spec(𝒪_{S,s})` is a scheme,
then `X` is a scheme. Here `f` is the unique structure morphism `toBase X`,
`s` is `Points.base x`, and `X ×_S Spec(𝒪_{S,s})` is
`baseChange (S.fromSpecStalk s) X`. -/
@[stacks 0B80]
theorem isScheme_of_forall_isScheme_baseChange_fromSpecStalk
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [QuasiCompact (toBase X)] [QuasiSeparated (toBase X)]
    (h_fromSpecStalk : ∀ x : Points X,
      IsScheme (baseChange (S.fromSpecStalk (Points.base x)) X)) :
    IsScheme X :=
  sorry

/-- The stalkwise scheme hypothesis of
`isScheme_of_forall_isScheme_baseChange_fromSpecStalk` is equivalent to
checking `IsScheme` only at images of points of `X` under `Points.base`. -/
theorem forall_isScheme_baseChange_fromSpecStalk_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (∀ x : Points X,
        IsScheme (baseChange (S.fromSpecStalk (Points.base x)) X)) ↔
      ∀ s : S, (∃ x : Points X, Points.base x = s) →
        IsScheme (baseChange (S.fromSpecStalk s) X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
