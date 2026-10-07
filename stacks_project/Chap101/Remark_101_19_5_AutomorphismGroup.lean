module

public import stacks_project.Chap101.Lemma_101_19_4_AutomorphismGroup

/-!
# Isomorphisms of automorphism groups at a point

A morphism `f : X ⟶ Y` of algebraic stacks induces an isomorphism of
automorphism groups at a point `x ∈ |X|` when the equivalent conditions of
Lemma 101.19.4 hold: the comparison `G_p ⟶ G_{p ≫ f}` is an isomorphism of
algebraic spaces for some, equivalently every, field-valued representative
of `x`. Literature also says that `f` is stabilizer preserving at `x` or
fixed-point reflecting at `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace automorphismGroup

/-- `f` induces an isomorphism between automorphism groups at `x` and
`Points.map f x`. This is the preferred packaging of the equivalent
conditions of Lemma 101.19.4; literature also says that `f` is stabilizer
preserving at `x` or fixed-point reflecting at `x`. -/
def IsIsoAt {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → IsIsoMap f p

/-- `IsIsoAt f x` means that the automorphism-group comparison along `f` is an
isomorphism at every field-valued representative of `x`. -/
theorem IsIsoAt_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) :
    IsIsoAt f x ↔ ∀ p : FieldValuedPoint X, Points.mk p = x → IsIsoMap f p :=
  sorry

/-- `IsIsoAt f x` if and only if some field-valued representative of `x` has
an isomorphic automorphism-group comparison along `f`. -/
theorem IsIsoAt_iff_exists {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) :
    IsIsoAt f x ↔ ∃ p : FieldValuedPoint X, Points.mk p = x ∧ IsIsoMap f p :=
  sorry

namespace IsIsoAt

/-- If `f` induces an isomorphism of automorphism groups at `x`, then the
comparison along `f` is an isomorphism at every field-valued representative
of `x`. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] {f : X ⟶ Y} {x : |X|} :
    IsIsoAt f x → ∀ p : FieldValuedPoint X, Points.mk p = x → IsIsoMap f p :=
  sorry

/-- If the automorphism-group comparison along `f` is an isomorphism at one
field-valued representative of `x`, then `f` induces an isomorphism of
automorphism groups at `x`. -/
theorem of_fieldValuedPoint {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : |X|}
    {p : FieldValuedPoint X} :
    Points.mk p = x → IsIsoMap f p → IsIsoAt f x :=
  sorry

end IsIsoAt

end automorphismGroup

/-- Literature synonym: a morphism of algebraic stacks is stabilizer
preserving at a point. -/
abbrev IsStabilizerPreservingAt {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) : Prop :=
  automorphismGroup.IsIsoAt f x

/-- Literature synonym: a morphism of algebraic stacks is fixed-point
reflecting at a point. -/
abbrev IsFixedPointReflectingAt {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) : Prop :=
  automorphismGroup.IsIsoAt f x

end AlgebraicGeometry.AlgebraicStack
