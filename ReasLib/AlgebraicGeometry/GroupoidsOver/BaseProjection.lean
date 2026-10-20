module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base

@[expose] public section

universe u

open CategoryTheory
open FiberedCategoryOver.Groupoids

namespace AlgebraicGeometry

/-- A morphism of categories fibred in groupoids over a scheme strictly commutes
with the canonical projections to the base fibration. -/
theorem comp_baseProjection {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    f ≫ baseProjection.{u + 1, u, u + 1} Y =
      baseProjection.{u + 1, u, u + 1} X :=
  sorry

end AlgebraicGeometry
