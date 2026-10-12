/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap71.Lemma_71_18_7_Blowup
public import stacks_project.Chap71.Lemma_71_18_7_Comparison

/-!
# Flattening morphisms of algebraic spaces by admissible blowups

A finite-type quasi-separated morphism of algebraic spaces that is flat and
locally of finite presentation over a quasi-compact open of a qcqs base becomes
flat and of finite presentation after a `U`-admissible blowup, on the strict
transform.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.39.1: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. Let `U ⊂ B` be an open subspace. Assume `B` is
quasi-compact and quasi-separated, `U` is quasi-compact, `f : X ⟶ B` is of
finite type and quasi-separated, and `f⁻¹(U) ⟶ U` is flat and locally of
finite presentation. Then there exists a `U`-admissible blowup `B' ⟶ B` such
that the strict transform `X'` of `X` is flat and of finite presentation over
`B'`. -/
@[stacks 087E]
theorem exists_isAdmissibleBlowup_flat_finitePresentation
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [FiniteType f] [QuasiSeparated f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [Flat (pullback.snd f U.ι)]
    [LocallyOfFinitePresentation (pullback.snd f U.ι)] :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        let f' := strictTransformSnd b (Z.inverseImage b) f
        Flat f' ∧ FinitePresentation f' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
