module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.21.3: a smooth morphism of schemes is regular. -/
@[stacks 07R9] #check
  (AlgebraicGeometry.instRegularOfSmooth :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Smooth f],
      AlgebraicGeometry.Regular f)
