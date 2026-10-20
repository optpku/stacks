module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-!
# Formal smoothness of representable morphisms of groupoid fibrations

For a morphism of categories fibred in groupoids representable by algebraic spaces,
formal smoothness on objects is equivalent to formal smoothness of every
scheme-slice representing morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects

/-- A morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is formally smooth on objects if and only if
every scheme-slice representing morphism of algebraic spaces is formally smooth. -/
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S} {p : X ⟶ Y}
    (hp : relativelyRepresentableByAlgebraicSpaces p) :
    FormallySmoothOnObjects p ↔ has (@AlgebraicSpace.FormallySmooth S) p :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects
