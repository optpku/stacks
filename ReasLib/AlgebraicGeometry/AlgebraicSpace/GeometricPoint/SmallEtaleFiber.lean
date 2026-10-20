module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import Mathlib.CategoryTheory.Elements
@[expose] public section
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A lift of a geometric point `xbar` of `X` through a scheme `U` étale over `X` is a
morphism of schemes over `S` from `Spec(xbar.K)` to `U` making the triangle over `X`
commute. -/
structure OverLift (xbar : GeometricPoint X) (U : smallEtaleSite X) where
  /-- The morphism of schemes over `S` lifting `xbar` through `U`. -/
  hom : Over.mk xbar.structureHom ⟶ U.left
  /-- The lift is compatible with the morphisms into `X`. -/
  fac : ofOverMap hom ≫ U.hom = xbar.hom

namespace OverLift

/-- Construct a lift of a geometric point through an étale scheme over `X`. -/
def of {xbar : GeometricPoint X} {U : smallEtaleSite X}
    (hom : Over.mk xbar.structureHom ⟶ U.left)
    (fac : ofOverMap hom ≫ U.hom = xbar.hom) : OverLift xbar U where
  hom := hom
  fac := fac

/-- The underlying morphism of `OverLift.of` is the supplied morphism over `S`. -/
theorem of_hom {xbar : GeometricPoint X} {U : smallEtaleSite X}
    (hom : Over.mk xbar.structureHom ⟶ U.left)
    (fac : ofOverMap hom ≫ U.hom = xbar.hom) :
    (of hom fac).hom = hom :=
  sorry

/-- A lift of `xbar` through `U` is a morphism of schemes over `S` whose image under
`ofOverMap` commutes with the structure morphisms into `X`. -/
theorem spec {xbar : GeometricPoint X} {U : smallEtaleSite X} (l : OverLift xbar U) :
    ofOverMap l.hom ≫ U.hom = xbar.hom :=
  sorry

/-- Postcompose a lift of a geometric point along a morphism in the small étale site. -/
def map {xbar : GeometricPoint X} {U V : smallEtaleSite X} (g : U ⟶ V)
    (l : OverLift xbar U) : OverLift xbar V :=
  of (l.hom ≫ g.left) sorry

/-- Postcomposition of lifts is composition of the underlying morphisms over `S`. -/
theorem map_hom {xbar : GeometricPoint X} {U V : smallEtaleSite X} (g : U ⟶ V)
    (l : OverLift xbar U) :
    (map g l).hom = l.hom ≫ g.left :=
  sorry

end OverLift

/-- The fiber functor of the small étale site of `X` at a geometric point, sending an étale
scheme over `X` to the type of lifts of that geometric point through the scheme. -/
noncomputable def toSmallEtalePoint_fiber (xbar : GeometricPoint X) :
    smallEtaleSite X ⥤ Type u where
  obj U := OverLift xbar U
  map {U V} (g : U ⟶ V) := TypeCat.ofHom fun (l : OverLift xbar U) ↦ OverLift.map g l
  map_id := sorry
  map_comp := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
