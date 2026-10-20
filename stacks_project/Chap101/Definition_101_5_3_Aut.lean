module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Automorphisms

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.5.3 (1): relative automorphisms of `x : Z ⟶ X`
are the pullback `Z ×_{x, X} I_{X/Y}`. -/
#check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.relativeAut :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X), GroupoidsOver S)
