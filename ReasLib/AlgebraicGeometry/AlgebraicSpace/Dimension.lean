module

public import ReasLib.Topology.KrullDimension.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Dimension of an algebraic space

The dimension of an algebraic space is the supremum of its étale-local dimensions at points.
This is not the topological Krull dimension of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dimension of an algebraic space at a point, as the supremum of local topological Krull
dimensions along étale morphisms from schemes through that point. This is not the local
topological Krull dimension of the space of points. -/
noncomputable def dimensionAt {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    WithBot ℕ∞ :=
  ⨆ (U : Over S) (f : ofOver U ⟶ X) (u : U.left)
    (_hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (_hx : Points.mapOfOver f u = x), topologicalKrullDimAt u

/-- The dimension of an algebraic space, as the supremum of its dimensions at points. This is not
the topological Krull dimension of the space of points. -/
noncomputable def dimension {S : Scheme.{u}} (X : AlgebraicSpace S) : WithBot ℕ∞ :=
  ⨆ x : Points X, dimensionAt x

/-- The dimension at a point equals the local topological Krull dimension of any étale scheme
chart through that point. -/
theorem dimensionAt_eq_topologicalKrullDimAt {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f) (u : U.left)
    {x : Points X} (hx : Points.mapOfOver f u = x) :
    dimensionAt x = topologicalKrullDimAt u :=
  sorry

namespace dimensionAt

/-- Every point of an algebraic space lies on an étale morphism from a scheme. -/
theorem exists_etale {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    ∃ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f ∧
        ∃ u : U.left, Points.mapOfOver f u = x :=
  sorry

end dimensionAt

/-- The dimension of an algebraic space is the supremum of its dimensions at points. -/
theorem dimension_eq_iSup_dimensionAt {S : Scheme.{u}} (X : AlgebraicSpace S) :
    dimension X = ⨆ x : Points X, dimensionAt x :=
  sorry

/-- On a scheme, viewed as an algebraic space, the dimension at a point is the usual local
topological Krull dimension. -/
theorem dimensionAt_ofOver {S : Scheme.{u}} (T : Over S) (t : T.left) :
    dimensionAt (ofOver.pointsEquiv T t) = topologicalKrullDimAt t :=
  sorry

/-- On a scheme, viewed as an algebraic space, the dimension is the usual topological Krull
dimension. -/
theorem dimension_ofOver {S : Scheme.{u}} (T : Over S) :
    dimension (ofOver T) = topologicalKrullDim T.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
