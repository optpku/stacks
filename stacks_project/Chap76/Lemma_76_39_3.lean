/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap71.Lemma_71_18_7_Blowup
public import stacks_project.Chap71.Lemma_71_18_7_Comparison

/-!
# Isomorphisms after admissible blowups of algebraic spaces

A proper morphism of algebraic spaces that is an isomorphism over a
quasi-compact open of a qcqs base becomes an isomorphism after a `U`-admissible
blowup, on the strict transform.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.39.3: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. Let `U ⊂ B` be an open subspace. Assume `B` is
quasi-compact and quasi-separated, `U` is quasi-compact, `f : X ⟶ B` is proper,
and `f⁻¹(U) ⟶ U` is an isomorphism. Then there exists a `U`-admissible blowup
`B' ⟶ B` such that the strict transform `X'` of `X` maps isomorphically to
`B'`. -/
@[stacks 0GUW]
theorem exists_isAdmissibleBlowup_strictTransform_isIso
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [Proper f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [IsIso (pullback.snd f U.ι)] :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        IsIso (strictTransformSnd b (Z.inverseImage b) f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
