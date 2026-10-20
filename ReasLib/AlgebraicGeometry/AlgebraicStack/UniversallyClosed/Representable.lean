module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of algebraic stacks representable by algebraic spaces has
universally closed scheme-slice representing morphisms if and only if every
algebraic-stack base change induces a closed map on underlying point spaces. -/
@[stacks 0512]
theorem has_universallyClosed_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversallyClosed S) f ↔ AlgebraicStack.UniversallyClosed f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
