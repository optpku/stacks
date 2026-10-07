module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCheckRecall

/-!
# Lemma 29.34.8

A smooth morphism is locally of finite presentation.

@stack 01VE
-/

@[expose] public section

universe u

/- Lemma 29.34.8

A smooth morphism is locally of finite presentation.
-/
@[stacks 01VE] #check
  (AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Smooth f],
      AlgebraicGeometry.LocallyOfFinitePresentation f)
