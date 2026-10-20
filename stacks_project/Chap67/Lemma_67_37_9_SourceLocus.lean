module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.SourceLocus

/-!
# Smooth source locus of a morphism of algebraic spaces

The largest open subspace of the source on which a morphism of algebraic spaces
is smooth, with its canonical open-subspace construction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.sourceLocus :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → OpenSubspace X)
