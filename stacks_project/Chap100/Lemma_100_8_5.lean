module

public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Definition_100_4_2_Points

/-!
# Monomorphisms induce injective maps of points

A monomorphism of algebraic stacks induces an injective map of sets of
points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.8.5: a monomorphism of algebraic stacks induces an injective map of
sets of points. -/
@[stacks 0500]
theorem Points.map_injective_of_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Mono f] :
    Function.Injective (Points.map f) :=
  sorry

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

end AlgebraicGeometry.AlgebraicStack
