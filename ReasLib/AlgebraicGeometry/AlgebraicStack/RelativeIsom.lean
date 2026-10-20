module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal.RelativeIsom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left exactness of relative automorphism presheaves

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

namespace AlgebraicGeometry.AlgebraicStack

/-- For a morphism of algebraic stacks, a map to the automorphism presheaf
factors uniquely through the relative automorphism presheaf if and only if its
image under the induced automorphism map is the identity section. -/
@[stacks 0CPJ]
theorem isomExactSequence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : Over S}
    (x : X.p.Fiber T) {G : (Over T)ᵒᵖ ⥤ Type (u + 1)}
    (φ : G ⟶ isom x x) :
    (∃! ψ : G ⟶ relativeIsom f x, ψ ≫ relativeIsom.ι f x = φ) ↔
      φ ≫ isomMap f x x = φ ≫ constIdentity f x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
