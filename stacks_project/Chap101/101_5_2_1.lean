module

public import stacks_project.Chap101.«101_5_2_1_RelativeIsom»
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
import Mathlib.Tactic.CrossRefAttribute

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

namespace AlgebraicGeometry.AlgebraicStack

/-- 101.5.2.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks over `S`, let
`T` be a scheme over `S`, and let `x` be an object of `X` over `T` with
`y = (fiberFunctor f T).obj x`. Then there is an exact sequence of sheaves of
groups `0 ⟶ Isom_{X/Y}(x, x) ⟶ Isom_X(x, x) ⟶ Isom_Y(y, y)`, where
`Isom_{X/Y}(x, x)` is `relativeIsom f x`, the first nonzero map is the kernel
inclusion `relativeIsom.ι f x`, and the second map is `isomMap f x x` against
the identity section `constIdentity f x`. -/
@[stacks 0CPJ]
theorem isomExactSequence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : Over S}
    (x : X.p.Fiber T) {G : (Over T)ᵒᵖ ⥤ Type (u + 1)}
    (φ : G ⟶ isom x x) :
    (∃! ψ : G ⟶ relativeIsom f x, ψ ≫ relativeIsom.ι f x = φ) ↔
      φ ≫ isomMap f x x = φ ≫ constIdentity f x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
