module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.DVRCodimZero
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.21.3: for a quasi-separated, finite-type morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S` with `Y` locally Noetherian, the following are
equivalent: `Proper f`; the valuative criterion of Definition 67.41.1; unique
dotted lifts in every valuative square `Spec(K) ⟶ X` over `Spec(A) ⟶ Y`; the same
unique lifts when `A` is a discrete valuation ring; and the same unique lifts when
`A` is a discrete valuation ring and the image of `Spec(K) ⟶ X` is a point of
codimension `0` on `X`. -/
@[stacks 0H1X] #check
  (AlgebraicGeometry.AlgebraicSpace.Proper.tfae_valuativeCriterion_dvr_codimZero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [QuasiSeparated f] → [FiniteType f] → [IsLocallyNoetherian Y] →
      List.TFAE [Proper f, ValuativeCriterion f,
        ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct,
        ValuativeCriterion.DVR f, ValuativeCriterion.DVR.AtCodimZero f])
