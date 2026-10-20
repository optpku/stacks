module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Submersive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of algebraic stacks representable by algebraic spaces has
universally submersive scheme-slice representing morphisms if and only if every
algebraic-stack base change induces a submersive map on underlying point spaces. -/
@[stacks 0CHX]
theorem has_universallySubmersive_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversallySubmersive S) f ↔ AlgebraicStack.UniversallySubmersive f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
