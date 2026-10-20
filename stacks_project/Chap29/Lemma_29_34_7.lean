module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth
import StacksCheckRecall

/-!
# Lemma 29.34.7

A smooth morphism is syntomic.

@stack 01VD
-/

@[expose] public section

universe u

/- Lemma 29.34.7: a smooth morphism is syntomic. -/
@[stacks 01VD] #check (AlgebraicGeometry.Smooth.syntomic :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y},
    AlgebraicGeometry.Smooth f → AlgebraicGeometry.Syntomic f)
