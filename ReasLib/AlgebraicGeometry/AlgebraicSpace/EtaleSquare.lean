/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

/-- An étale scheme square over a morphism of algebraic spaces consists of one chart on each
space and a commuting morphism of schemes over the base. -/
structure Square {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) where
  /-- The chart on the source algebraic space. -/
  source : site X
  /-- The chart on the target algebraic space. -/
  target : site Y
  /-- The morphism between the underlying schemes over the base. -/
  map : source.left ⟶ target.left
  /-- The two maps from the source chart to the target space coincide. -/
  comm : yoneda.map map ≫ target.hom = source.hom ≫ f

/-- Construct an étale square from two charts and a commuting scheme morphism. -/
def Square.ofSchemeMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (source : site X) (target : site Y) (map : source.left ⟶ target.left)
    (comm : yoneda.map map ≫ target.hom = source.hom ≫ f) : Square f :=
  ⟨source, target, map, comm⟩

/-- The square constructed from a scheme morphism has the specified charts, scheme map,
and commuting composite. -/
theorem Square.ofSchemeMap_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (source : site X) (target : site Y) (map : source.left ⟶ target.left)
    (comm : yoneda.map map ≫ target.hom = source.hom ≫ f) :
    let square := Square.ofSchemeMap f source target map comm
    square.source = source ∧ square.target = target ∧ square.map = map ∧
      yoneda.map square.map ≫ square.target.hom = square.source.hom ≫ f := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
