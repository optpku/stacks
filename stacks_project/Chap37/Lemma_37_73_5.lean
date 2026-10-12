/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification.AffineOpenCover
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 37.73.5: for a nonempty separated scheme with an affine open cover indexed by
`Fin (n + 1)`, the affine stratification number is at most `n`. -/
@[stacks 0F2W] #check
  (AlgebraicGeometry.Scheme.FiniteAffineStratification.number_le_of_hasCard :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [Nonempty X] [X.IsSeparated] {n : ℕ}
      (h_cover : AlgebraicGeometry.Scheme.AffineOpenCover.HasCard X (n + 1)),
      -- Local instance justification (proof-local temporary data): the finite affine cover supplies the compactness required by the canonical stratification number.
      letI : CompactSpace X :=
        AlgebraicGeometry.Scheme.AffineOpenCover.compactSpace_of_hasCard h_cover
      AlgebraicGeometry.Scheme.FiniteAffineStratification.number X ≤ n)
