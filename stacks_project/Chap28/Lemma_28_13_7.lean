/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Closed
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 28.13.7

The closed-subscheme criterion for Nagata schemes lives in
`ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Closed`.
-/

universe u

/- Lemma 28.13.7: a locally Noetherian scheme is Nagata if and only if every
integral closed subscheme is Japanese. -/
@[stacks 033Y] #check
  (AlgebraicGeometry.Scheme.nagata_iff_forall_integral_closedSubscheme_japanese :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      AlgebraicGeometry.Scheme.Nagata X ↔
        ∀ ⦃Z : AlgebraicGeometry.Scheme.{u}⦄ (i : Z ⟶ X)
          [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsIntegral Z],
          AlgebraicGeometry.Scheme.IsJapanese Z)
