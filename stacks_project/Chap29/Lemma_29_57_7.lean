module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Immersion
import StacksCheckRecall

open CategoryTheory

/- Lemma 29.57.7: An immersion has universally bounded fibres. -/
@[stacks 03J9] #check
  (AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres_of_isImmersion :
    ∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsImmersion f],
      AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres f)
