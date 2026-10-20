module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.CohenMacaulay
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 48.25.4: A Gorenstein morphism is Cohen-Macaulay. -/
@[stacks 0C06] #check
  (AlgebraicGeometry.Gorenstein.instCohenMacaulay :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Gorenstein f], AlgebraicGeometry.CohenMacaulay f)
