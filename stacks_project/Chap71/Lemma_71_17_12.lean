/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap71.Lemma_71_18_7_Blowup

/-!
# Composition of successive finite-presentation blowups

Successive blowups of a quasi-compact quasi-separated algebraic space in
finitely presented closed subspaces compose to a blowup in a finitely presented
closed subspace whose underlying point-set is the union of the first center and
the image of the second.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBlowup

/-- Lemma 71.17.12: let `S` be a scheme and let `X` be a quasi-compact
quasi-separated algebraic space over `S`. Let `Z ⊂ X` be a closed subspace of
finite presentation, let `b : X' ⟶ X` be a blowup of `X` in `Z`, let `Z' ⊂ X'`
be a closed subspace of finite presentation, and let `b' : X'' ⟶ X'` be a
blowup of `X'` in `Z'`. There exists a closed subspace `Y ⊂ X` of finite
presentation such that `Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet`
and `b' ≫ b` is a blowup of `X` in `Y`. -/
@[stacks 0860]
theorem exists_center_comp {S : Scheme.{u}} {X X' X'' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Z : ClosedSubspace X) [FinitePresentation Z.ι]
    (b : X' ⟶ X) [IsBlowup b Z]
    (Z' : ClosedSubspace X') [FinitePresentation Z'.ι]
    (b' : X'' ⟶ X') [IsBlowup b' Z'] :
    ∃ Y : ClosedSubspace X,
      FinitePresentation Y.ι ∧
        Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet ∧
          IsBlowup (b' ≫ b) Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBlowup
