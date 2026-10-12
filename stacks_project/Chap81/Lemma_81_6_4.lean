/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Lemma 81.6.4

In a commutative diagram of algebraic spaces, if the left and outer squares
are cartesian and the bottom-left map is surjective étale, then the right
square is cartesian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.6.4: Let `S` be a scheme. Let `A ⟶ C ⟶ E` over `B ⟶ D ⟶ F` be a
commutative diagram of algebraic spaces over `S`. If the left square `A, B, C, D`
and the outer square `A, B, E, F` are cartesian and `B ⟶ D` is surjective étale,
then the right square `C, D, E, F` is cartesian. -/
@[stacks 07VZ]
theorem isPullback_of_left_of_surjective_etale
    {S : Scheme.{u}} {A B C D E F : AlgebraicSpace S}
    {fAC : A ⟶ C} {fAB : A ⟶ B} {fCD : C ⟶ D} {fBD : B ⟶ D}
    {fCE : C ⟶ E} {fEF : E ⟶ F} {fDF : D ⟶ F}
    (hABCD : IsPullback fAC fAB fCD fBD)
    (hABEF : IsPullback (fAC ≫ fCE) fAB fEF (fBD ≫ fDF))
    (wCDEF : fCE ≫ fEF = fCD ≫ fDF) [Surjective fBD] [Etale fBD] :
    IsPullback fCE fCD fEF fDF :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
