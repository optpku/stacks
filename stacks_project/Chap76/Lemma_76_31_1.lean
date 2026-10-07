module

public import stacks_project.Chap76.Lemma_76_31_1_FiberDimension

/-!
# Dimension of fibres of finite type morphisms of algebraic spaces

For a finite type morphism of algebraic spaces, the target-indexed fibre
dimension at a point equals the dimension of any field-valued fibre over a
representative of that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.31.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a finite type
morphism of algebraic spaces over `S`. Let `y` be a point of `Y`, represented
by a field-valued point `p`. Then the fibre dimension of `f` at `y` equals the
dimension of the algebraic space `fieldFiber f p`.

Quantity (1) is `fiberDimension f (Points.mk p)`, equal to `⊥` when
`Points.mk p` is not in the image of `Points.map f`, and otherwise the least
`d : ℕ` such that `f` has relative dimension at most `d` at every point of `X`
mapping to `y`. Quantity (2) is `dimension (fieldFiber f p)` for any
representative `p` of `y`. -/
@[stacks 0D4M]
theorem fiberDimension_eq_dimension_fieldFiber {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (p : FieldValuedPoint Y) :
    fiberDimension f (Points.mk p) = dimension (fieldFiber f p) :=
  sorry

/-- The identification of fibre dimension with the dimension of
`Spec(k) ×_Y X` for a representative morphism `Spec(k) ⟶ Y`. -/
theorem fiberDimension_eq_dimension_fieldFiber_of {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S)
    (g : ofOver (Over.mk σ) ⟶ Y) :
    fiberDimension f (Points.mk (FieldValuedPoint.of k σ g)) =
      dimension (fieldFiber f (FieldValuedPoint.of k σ g)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
