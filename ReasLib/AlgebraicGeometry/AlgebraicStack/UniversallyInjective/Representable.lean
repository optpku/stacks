module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Representable universally injective morphisms of algebraic stacks

Universal injectivity of scheme-slice representing morphisms characterizes
universal injectivity of a morphism of algebraic stacks representable by
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of algebraic stacks representable by algebraic spaces has
universally injective scheme-slice representing morphisms if and only if every
algebraic-stack base change induces an injective map on underlying points. -/
@[stacks 0CI1]
theorem has_universallyInjective_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversallyInjective S) f ↔
      AlgebraicStack.UniversallyInjective f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
