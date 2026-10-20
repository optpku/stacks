module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Comparison maps to open complements

The inverse image of the open complement of a closed subset maps to that
complement by the second pullback projection.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Open

/-- The comparison from the inverse image of the open complement of a closed
subset to that complement is the second pullback projection. -/
noncomputable def complementComparison {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    openInverseImage f (OpenSubspace.Construction.ι X T.compl) ⟶
      OpenSubspace.Construction.space X T.compl :=
  inverseImageTo f (OpenSubspace.Construction.ι X T.compl)
    (OpenSubspace.Construction.inclusion_isOpenImmersion X T.compl).presheaf

/-- The comparison to an open complement agrees with the canonical comparison
of the inverse-image open subspace. -/
theorem complementComparison_eq {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    complementComparison f T =
      openInverseImageTo f (OpenSubspace.Construction.ι X T.compl) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Open

namespace AlgebraicGeometry.AlgebraicSpace

/-- The open algebraic subspace complementary to a closed subset of points. -/
noncomputable abbrev openComplementAlong {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) : AlgebraicSpace S :=
  OpenSubspace.Construction.space X T.compl

/-- The canonical inclusion of the open complement of a closed subset. -/
noncomputable abbrev openComplementι {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) : openComplementAlong X T ⟶ X :=
  OpenSubspace.Construction.ι X T.compl

/-- The functor of points of the open complement is the subfunctor of sections
whose images lie in that complement. -/
theorem openComplementAlong_functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    (openComplementAlong X T).functorOfPoints =
      (OpenSubspace.Construction.subfunctor X T.compl).toFunctor :=
  rfl

/-- The image on points of the open complement inclusion is the complementary set. -/
theorem openComplementAlong_pointsSet {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    Set.range (Points.map (openComplementι X T)) = (T : Set (Points X))ᶜ :=
  OpenSubspace.Construction.inclusion_range X T.compl

end AlgebraicGeometry.AlgebraicSpace
