/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup

/-!
# Common admissible blowups of algebraic spaces

Open immersions of finite-type separated algebraic spaces over a qcqs base
can be realized, after `U`-admissible blowups, as open immersions into a
common finite-type separated algebraic space over that base.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.40.1: Let `S` be a scheme. Let `Y` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `ι1 : U ⟶ X1` and `ι2 : U ⟶ X2`
be open immersions of algebraic spaces over `Y`, and assume `U`, `X1`, `X2`
are of finite type and separated over `Y`. Then there exists a commutative
diagram of algebraic spaces over `Y` in which `X1' ⟶ X1` and `X2' ⟶ X2` are
`U`-admissible blowups, `X1' ⟶ X` and `X2' ⟶ X` are open immersions, and
`X ⟶ Y` is separated of finite type. -/
@[stacks 088Q]
theorem exists_isAdmissibleBlowup_isOpenImmersion
    {S : Scheme.{u}} {Y U X1 X2 : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f1 : X1 ⟶ Y) (f2 : X2 ⟶ Y) (fU : U ⟶ Y)
    [FiniteType f1] [FiniteType f2] [FiniteType fU]
    [Separated f1] [Separated f2] [Separated fU]
    (ι1 : U ⟶ X1) (ι2 : U ⟶ X2)
    [IsOpenImmersion ι1] [IsOpenImmersion ι2]
    (hι1 : ι1 ≫ f1 = fU) (hι2 : ι2 ≫ f2 = fU) :
    ∃ (X1' X2' X : AlgebraicSpace S)
      (b1 : X1' ⟶ X1) (b2 : X2' ⟶ X2)
      (j1 : X1' ⟶ X) (j2 : X2' ⟶ X) (pX : X ⟶ Y)
      (u1' : U ⟶ X1') (u2' : U ⟶ X2') (uX : U ⟶ X),
      IsAdmissibleBlowup (OpenSubspace.ofι ι1) b1 ∧
        IsAdmissibleBlowup (OpenSubspace.ofι ι2) b2 ∧
        IsOpenImmersion j1 ∧ IsOpenImmersion j2 ∧
        FiniteType pX ∧ Separated pX ∧
        u1' ≫ b1 = ι1 ∧ u2' ≫ b2 = ι2 ∧
        u1' ≫ j1 = uX ∧ u2' ≫ j2 = uX ∧
        j1 ≫ pX = b1 ≫ f1 ∧ j2 ≫ pX = b2 ≫ f2 ∧
        uX ≫ pX = fU :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
