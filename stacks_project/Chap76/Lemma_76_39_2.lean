/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap71.Lemma_71_18_7_Blowup
public import stacks_project.Chap71.Lemma_71_18_7_Comparison

/-!
# Finite locally free morphisms of algebraic spaces after admissible blowups

A proper morphism of algebraic spaces that is finite locally free over a
quasi-compact open of a qcqs base becomes finite locally free after a
`U`-admissible blowup, on the strict transform.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.39.2: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. Let `U ⊂ B` be an open subspace. Assume `B` is
quasi-compact and quasi-separated, `U` is quasi-compact, `f : X ⟶ B` is proper,
and `f⁻¹(U) ⟶ U` is finite locally free. Then there exists a `U`-admissible
blowup `B' ⟶ B` such that the strict transform `X'` of `X` is finite locally
free over `B'`. -/
@[stacks 0B4K]
theorem exists_isAdmissibleBlowup_finiteLocallyFree
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [Proper f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [FiniteLocallyFree (pullback.snd f U.ι)] :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        FiniteLocallyFree (strictTransformSnd b (Z.inverseImage b) f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
