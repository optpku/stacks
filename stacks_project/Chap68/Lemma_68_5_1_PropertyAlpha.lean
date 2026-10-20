module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyAlpha

/-!
# Property (α) for algebraic spaces

An algebraic space has property (α) when every point satisfies the affine étale
finite-fibre test of Lemma 68.4.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.HasPropertyAlpha :
  {S : Scheme.{u}} → AlgebraicSpace S → Prop)
