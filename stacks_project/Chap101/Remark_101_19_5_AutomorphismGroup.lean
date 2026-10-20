module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup

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

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y], (X ⟶ Y) → |X| → Prop)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|),
    IsIsoAt f x ↔ ∀ p : FieldValuedPoint X, Points.mk p = x → IsIsoMap f p)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt_iff_exists :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|),
    IsIsoAt f x ↔ ∃ p : FieldValuedPoint X, Points.mk p = x ∧ IsIsoMap f p)

namespace IsIsoAt

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] {f : X ⟶ Y} {x : |X|},
    IsIsoAt f x → ∀ p : FieldValuedPoint X, Points.mk p = x → IsIsoMap f p)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt.of_fieldValuedPoint :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : |X|}
    {p : FieldValuedPoint X},
    Points.mk p = x → IsIsoMap f p → IsIsoAt f x)

end IsIsoAt

end automorphismGroup

#check (AlgebraicGeometry.AlgebraicStack.IsStabilizerPreservingAt :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → |X| → Prop)

#check (AlgebraicGeometry.AlgebraicStack.IsFixedPointReflectingAt :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → |X| → Prop)

end AlgebraicGeometry.AlgebraicStack
