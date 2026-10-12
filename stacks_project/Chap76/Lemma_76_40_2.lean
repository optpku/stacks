/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Lemma_69_20_1_ProjectiveSpace
public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup

/-!
# Chow embeddings after admissible blowups of algebraic spaces

A finite-type separated morphism of algebraic spaces over a qcqs base that
immerses a quasi-compact open into projective space over that base becomes,
after a `U`-admissible blowup, an open immersion into a proper representable
space obtained by blowing up a closed subspace of that projective space.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.40.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `U ⊂ X` be an open subspace. Assume `U` is
quasi-compact, `Y` is quasi-compact and quasi-separated, there exists an
immersion `i : U.X ⟶ ProjectiveSpace n Y` over `Y`, and `f` is of finite type
and separated. Then there exists a commutative diagram in which the arrows
with source `U.X` are open immersions, `X' ⟶ X` is a `U`-admissible blowup,
`X' ⟶ Z'` is an open immersion, and `Z' ⟶ Y` is a proper representable
morphism of algebraic spaces. More precisely, `Z' ⟶ Z` is a `U`-admissible
blowup and `Z ⟶ ProjectiveSpace n Y` is a closed immersion. -/
@[stacks 088R]
theorem exists_isAdmissibleBlowup_closedImmersion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [FiniteType f] [Separated f]
    (U : OpenSubspace X) [IsQuasiCompact U.X]
    (n : ℕ) (i : U.X ⟶ ProjectiveSpace n Y) [IsImmersion i]
    (h_over : i ≫ ProjectiveSpace.toBase n Y = U.ι ≫ f) :
    ∃ (X' Z' Z : AlgebraicSpace S)
      (bX : X' ⟶ X) (j : X' ⟶ Z') (bZ : Z' ⟶ Z)
      (c : Z ⟶ ProjectiveSpace n Y)
      (ιX' : U.X ⟶ X') (ιZ' : U.X ⟶ Z') (ιZ : U.X ⟶ Z)
      (hιX' : IsOpenImmersion ιX') (hιZ' : IsOpenImmersion ιZ')
      (hιZ : IsOpenImmersion ιZ),
      IsAdmissibleBlowup U bX ∧ IsOpenImmersion j ∧
        Proper (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) ∧
        yoneda.relativelyRepresentable (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) ∧
        IsAdmissibleBlowup ⟨U.X, ιZ, hιZ⟩ bZ ∧
        IsClosedImmersion c ∧
        ιX' ≫ bX = U.ι ∧ ιX' ≫ j = ιZ' ∧ ιZ' ≫ bZ = ιZ ∧
        ιZ ≫ c = i ∧
        bX ≫ f = j ≫ bZ ≫ c ≫ ProjectiveSpace.toBase n Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
