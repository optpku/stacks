module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

namespace AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects

/-- An open immersion of categories fibred in groupoids over `(Sch/S)_fppf`
is limit preserving on objects. -/
@[stacks 06CY]
instance of_openImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [OpenImmersion p] : LimitPreservingOnObjects p :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
