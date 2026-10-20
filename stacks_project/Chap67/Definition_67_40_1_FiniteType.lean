module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Finite type morphisms of algebraic spaces

The canonical public owner defines locally finite type by the étale scheme-square
condition and finite type by adding quasi-compactness, as in Stacks Definition
67.23.1 (1) and (3), tag 03XF.
-/

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
