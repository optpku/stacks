module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCheckRecall

/-!
# Lemma 29.34.9

A smooth morphism is flat.

@stack 01VF
-/

@[expose] public section

universe u

/- Lemma 29.34.9

A smooth morphism is flat.
-/
@[stacks 01VF] #check
  (AlgebraicGeometry.instFlatOfSmooth :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Smooth f],
      AlgebraicGeometry.Flat f)
