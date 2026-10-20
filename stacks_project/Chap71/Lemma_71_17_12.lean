module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Composition

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

/- Lemma 71.17.12: let `S` be a scheme and let `X` be a quasi-compact
quasi-separated algebraic space over `S`. Let `Z ⊂ X` be a closed subspace of
finite presentation, let `b : X' ⟶ X` be a blowup of `X` in `Z`, let `Z' ⊂ X'`
be a closed subspace of finite presentation, and let `b' : X'' ⟶ X'` be a
blowup of `X'` in `Z'`. There exists a closed subspace `Y ⊂ X` of finite
presentation such that `Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet`
and `b' ≫ b` is a blowup of `X` in `Y`. -/
@[stacks 0860] #check
  (AlgebraicGeometry.AlgebraicSpace.IsBlowup.exists_center_comp :
    ∀ {S : Scheme.{u}} {X X' X'' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Z : ClosedSubspace X) [FinitePresentation Z.ι]
    (b : X' ⟶ X) [IsBlowup b Z]
    (Z' : ClosedSubspace X') [FinitePresentation Z'.ι]
    (b' : X'' ⟶ X') [IsBlowup b' Z'],
    ∃ Y : ClosedSubspace X,
      FinitePresentation Y.ι ∧
        Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet ∧
          IsBlowup (b' ≫ b) Y)
