module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldPoints

/-!
# Injectivity on field-valued points of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is injective on
field-valued points when, for every field `K` over `S`, postcomposition with `f`
is injective on `Mor_S(Spec K, X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.injectiveOnFieldPoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
