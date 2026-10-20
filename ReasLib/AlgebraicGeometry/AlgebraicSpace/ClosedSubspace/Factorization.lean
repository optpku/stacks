module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-!
# Factorization through closed subspaces of algebraic spaces

A morphism from a reduced algebraic space factors through a closed immersion if and
only if the induced map on points lands in the image of that immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsClosedImmersion

/-- A morphism from a reduced algebraic space factors through a closed immersion if and
only if its image on points is contained in the image of that immersion. -/
theorem exists_lift_iff_range_subset {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsReduced Y] (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i) :=
  sorry

/-- A morphism from a reduced algebraic space factors uniquely through a closed immersion
if and only if its image on points is contained in the image of that immersion. -/
theorem existsUnique_lift_iff_range_subset {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsReduced Y] (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i) :=
  sorry

end IsClosedImmersion

namespace ClosedSubspace

/-- A morphism from a reduced algebraic space factors through a closed subspace if and only if
its image on points is contained in the image of the subspace inclusion. -/
theorem exists_lift_iff_range_subset {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsReduced Y] (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z.X, g ≫ Z.ι = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map Z.ι) :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
