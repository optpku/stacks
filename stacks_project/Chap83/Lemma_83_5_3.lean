module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Orbit
import StacksCheckRecall

/-!
# Invariant morphisms are constant on point-set orbits
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 83.5.3: in the situation of Definition 83.5.1, an `R`-invariant morphism
`φ : U ⟶ X` of algebraic spaces over `B` induces a map `|φ| : |U| → |X|` that is
constant on `R`-orbits in `|U|`. -/
@[stacks 048P] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.pointsMap_eq_of_mem_pointsOrbit :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
      (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U) {φ : U ⟶ X},
      P.t ≫ φ = P.s ≫ φ → ∀ {u u' : Points U.left},
        u' ∈ P.pointsOrbit u → Points.map φ.left u = Points.map φ.left u')

/- An `R`-invariant morphism equalizes the two projections, so `|φ|` is constant along
a one-step `|R|`-edge. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.pointsMap_eq_of_pointsRel :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
      (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U) {φ : U ⟶ X},
      P.t ≫ φ = P.s ≫ φ → ∀ {u u' : Points U.left},
        P.pointsRel u u' → Points.map φ.left u = Points.map φ.left u')
