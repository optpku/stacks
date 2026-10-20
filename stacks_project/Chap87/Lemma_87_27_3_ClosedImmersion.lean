module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion

/-!
# Closed immersions of formal algebraic spaces

A morphism of functors of points on schemes over `S` is a closed immersion
when it is representable by algebraic spaces and every Yoneda pullback is a
closed immersion of algebraic spaces, in the sense of Bootstrap, Definition
03XZ.

The closed-immersion API is provided by the canonical mathematical owner.
-/

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)
