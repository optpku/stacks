module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom

/-!
# Equation 101.5.2.1 — left-exact sequence of Isom sheaves

For a morphism of algebraic stacks, the relative automorphism sheaf is the
kernel of the canonical map `Isom_X(x, x) ⟶ Isom_Y(y, y)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
open scoped Bicategory

noncomputable section

universe u

/- 101.5.2.1: For a morphism of algebraic stacks, the relative automorphism
sheaf is the kernel of the map on automorphism sheaves at the identity. -/
@[stacks 0CPJ] #check (AlgebraicGeometry.AlgebraicStack.isomExactSequence :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : Over S}
      (x : X.p.Fiber T) {G : (Over T)ᵒᵖ ⥤ Type (u + 1)}
      (φ : G ⟶ isom x x),
      (∃! ψ : G ⟶ relativeIsom f x, ψ ≫ relativeIsom.ι f x = φ) ↔
        φ ≫ isomMap f x x = φ ≫ constIdentity f x)
