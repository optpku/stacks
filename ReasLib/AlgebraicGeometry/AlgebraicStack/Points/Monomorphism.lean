module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism

/-!
# Monomorphisms induce injective maps of points

A monomorphism of algebraic stacks reflects equivalence of field-valued points
and induces an injective map on their equivalence classes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace FieldValuedPoint

/-- Two field-valued points of an algebraic stack become equivalent after
postcomposition with a monomorphism if and only if they were already
equivalent. -/
theorem Equivalent.map_iff_of_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {p q : FieldValuedPoint X}
    (f : X ⟶ Y) [Groupoids.Hom.Mono f] :
    Equivalent (p.map f) (q.map f) ↔ Equivalent p q :=
  sorry

end FieldValuedPoint

/-- A monomorphism of algebraic stacks induces an injective map on points. -/
@[stacks 0500]
theorem Points.map_injective_of_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Mono f] :
    Function.Injective (Points.map f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
