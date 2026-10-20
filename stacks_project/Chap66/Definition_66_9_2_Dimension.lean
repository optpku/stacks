module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension

/-!
# Dimension of an algebraic space

The pointwise and global dimension API is provided by its canonical mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.dimensionAt : Points X → WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.dimension X : WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.dimensionAt_eq_topologicalKrullDimAt :
  ∀ {U : Over S} (f : ofOver U ⟶ X),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f →
    ∀ (u : U.left) {x : Points X}, Points.mapOfOver f u = x →
      dimensionAt x = topologicalKrullDimAt u)

#check (AlgebraicGeometry.AlgebraicSpace.dimensionAt.exists_etale :
  ∀ x : Points X, ∃ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f ∧
        ∃ u : U.left, Points.mapOfOver f u = x)

#check (AlgebraicGeometry.AlgebraicSpace.dimension_eq_iSup_dimensionAt X :
  dimension X = ⨆ x : Points X, dimensionAt x)

#check (AlgebraicGeometry.AlgebraicSpace.dimensionAt_ofOver :
  ∀ (T : Over S) (t : T.left),
    dimensionAt (ofOver.pointsEquiv T t) = topologicalKrullDimAt t)

#check (AlgebraicGeometry.AlgebraicSpace.dimension_ofOver :
  ∀ T : Over S, dimension (ofOver T) = topologicalKrullDim T.left)

end AlgebraicGeometry.AlgebraicSpace
