module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Diagram data for morphisms of lifts of algebraic stacks

Two algebraic-space maps `(f, f')` form a diagram over `W` when `f` is over
`W` and `f'` restricts to `f`. A 2-isomorphism makes the right triangle
over `X'` commute.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}} {X' : GroupoidsOver S}

/-- Diagram data between `(V, V', b, j, y')` and `(U, U', a, i, x')`
consists of a map `f : V ⟶ U` over `W`, a map `f' : V' ⟶ U'` restricting
to `f`, and a 2-isomorphism in the right triangle over `X'`. -/
structure Hom [AlgebraicStack X'] {W U U' V V' : AlgebraicSpace S}
    (a : U ⟶ W) (i : U ⟶ U') (x' : U'.toGroupoids ⟶ X')
    (b : V ⟶ W) (j : V ⟶ V') (y' : V'.toGroupoids ⟶ X') where
  /-- Package the space maps, commutativity equalities, and right-triangle 2-isomorphism. -/
  of ::
  /-- The morphism of algebraic spaces `f : V ⟶ U` over `W`. -/
  f : V ⟶ U
  /-- The morphism of algebraic spaces `f' : V' ⟶ U'` restricting to `f`. -/
  f' : V' ⟶ U'
  /-- `f` is a morphism over `W`. -/
  overW : f ≫ a = b
  /-- The restriction of `f'` along `j` is `f` along `i`. -/
  restrict : j ≫ f' = f ≫ i
  /-- The 2-cell `γ : AlgebraicSpace.toGroupoids.map f' ≫ x' ≅ y'` of the right triangle. -/
  triangle : AlgebraicSpace.toGroupoids.map f' ≫ x' ≅ y'

namespace Hom

variable [AlgebraicStack X'] {W U U' V V' : AlgebraicSpace S}
variable {a : U ⟶ W} {i : U ⟶ U'} {x' : U'.toGroupoids ⟶ X'}
variable {b : V ⟶ W} {j : V ⟶ V'} {y' : V'.toGroupoids ⟶ X'}

/-- Package space maps `f`, `f'`, their commutativity equalities, and the right-triangle
2-isomorphism as diagram data. -/
def mk (f : V ⟶ U) (f' : V' ⟶ U')
    (overW : f ≫ a = b) (restrict : j ≫ f' = f ≫ i)
    (triangle : AlgebraicSpace.toGroupoids.map f' ≫ x' ≅ y') :
    Hom a i x' b j y' :=
  of f f' overW restrict triangle

/-- The diagram data has `f` over `W` and `f'` restricting to `f`. -/
theorem spec (h : Hom a i x' b j y') :
    h.f ≫ a = b ∧ j ≫ h.f' = h.f ≫ i := sorry

/-- The diagram data is reconstructed from its space maps, commutativity
equalities, and right-triangle 2-isomorphism. -/
theorem iff (h : Hom a i x' b j y') :
    h = mk h.f h.f' h.overW h.restrict h.triangle := sorry

/-- The over-`W` triangle is the commutative square with identity on `V`. -/
theorem commSq_overW (h : Hom a i x' b j y') : CommSq h.f (𝟙 V) a b := sorry

/-- Restriction of `f'` to `V` is the commutative square with `j`, `f`, `f'`, `i`. -/
theorem commSq_restrict (h : Hom a i x' b j y') : CommSq j h.f h.f' i := sorry

end Hom

end AlgebraicGeometry.AlgebraicStack.Lift
