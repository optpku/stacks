module

public import stacks_project.Chap83.Definition_83_5_1_Orbit

/-!
# Invariant morphisms are constant on point-set orbits
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- Lemma 83.5.3: in the situation of Definition 83.5.1, an `R`-invariant morphism
`φ : U ⟶ X` of algebraic spaces over `B` induces a map `|φ| : |U| → |X|` that is
constant on `R`-orbits in `|U|`. -/
@[stacks 048P]
theorem pointsMap_eq_of_mem_pointsOrbit {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.t ≫ φ = P.s ≫ φ)
    {u u' : Points U.left} (h : u' ∈ P.pointsOrbit u) :
    Points.map φ.left u = Points.map φ.left u' :=
  sorry

/-- An `R`-invariant morphism equalizes the two projections, so `|φ|` is constant along
a one-step `|R|`-edge. -/
theorem pointsMap_eq_of_pointsRel {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.t ≫ φ = P.s ≫ φ)
    {u u' : Points U.left} (h : P.pointsRel u u') :
    Points.map φ.left u = Points.map φ.left u' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
