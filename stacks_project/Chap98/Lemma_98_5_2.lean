module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RimSchlessinger
import StacksCheckRecall

/-!
# Algebraic stacks satisfy the Rim-Schlessinger condition

An algebraic stack over a locally Noetherian scheme satisfies condition (RS).
-/

@[expose] public section

universe u

/- Lemma 98.5.2: an algebraic stack over a locally Noetherian scheme satisfies
the Rim-Schlessinger condition. -/
@[stacks 07WQ] #check (AlgebraicGeometry.GroupoidsOver.instHasRimSchlessinger_algebraicStack :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (X : AlgebraicGeometry.GroupoidsOver S) [AlgebraicGeometry.AlgebraicStack X],
    AlgebraicGeometry.GroupoidsOver.HasRimSchlessinger X)
