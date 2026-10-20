module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.Smooth
import StacksCheckRecall

/-!
# Smooth morphisms of algebraic spaces are syntomic
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.37.8: A smooth morphism of algebraic spaces is syntomic. -/
@[stacks 06CP] #check (AlgebraicGeometry.AlgebraicSpace.Smooth.syntomic :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Smooth f], AlgebraicGeometry.AlgebraicSpace.Syntomic f)
