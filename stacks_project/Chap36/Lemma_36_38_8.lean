/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.ProjectionFormula
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.38.8: proper pushforward on coherent `K₀'` satisfies the projection formula
with pullback on perfect `K₀`. -/
@[stacks 0FDM] #check
  (AlgebraicGeometry.Scheme.K0'.projectionFormula :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsLocallyNoetherian Y]
      [AlgebraicGeometry.IsProper f]
      (α : AlgebraicGeometry.Scheme.K0' X) (β : AlgebraicGeometry.Scheme.K0 Y),
      AlgebraicGeometry.Scheme.K0'.pushforward f
          (AlgebraicGeometry.Scheme.K0'.Action.act X
            (AlgebraicGeometry.Scheme.K0.pullback f β) α) =
        AlgebraicGeometry.Scheme.K0'.Action.act Y β
          (AlgebraicGeometry.Scheme.K0'.pushforward f α))
