/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary

/-- A pointed elementary étale refinement square over a morphism of schemes. -/
structure RefinementSquare {Y S : Scheme.{u}} (f : Y ⟶ S) (y : Y) where
  /-- The elementary étale neighbourhood of the source point. -/
  source : EtaleNeighborhood.Elementary Y y
  /-- The elementary étale neighbourhood of the image point. -/
  base : EtaleNeighborhood.Elementary S (f y)
  /-- The comparison morphism between the schemes underlying the two neighbourhoods. -/
  map : source.obj.toEtale.left ⟶ base.obj.toEtale.left
  /-- The comparison morphism forms a commutative square with the structural morphisms. -/
  comm : CommSq source.obj.toEtale.hom map f base.obj.toEtale.hom
  /-- The comparison morphism preserves the selected points. -/
  map_point : map source.obj.point = base.obj.point

namespace RefinementSquare

/-- Construct a pointed elementary étale refinement square from its components. -/
def ofComponents {Y S : Scheme.{u}} (f : Y ⟶ S) (y : Y)
    (source : EtaleNeighborhood.Elementary Y y)
    (base : EtaleNeighborhood.Elementary S (f y))
    (map : source.obj.toEtale.left ⟶ base.obj.toEtale.left)
    (comm : CommSq source.obj.toEtale.hom map f base.obj.toEtale.hom)
    (map_point : map source.obj.point = base.obj.point) : RefinementSquare f y where
  source := source
  base := base
  map := map
  comm := comm
  map_point := map_point

/-- A pointed elementary étale refinement square consists of elementary neighbourhoods,
a commutative square of structural morphisms, and a point-preserving comparison map. -/
theorem spec {Y S : Scheme.{u}} {f : Y ⟶ S} {y : Y} (sq : RefinementSquare f y) :
    sq.source.obj.IsElementary ∧ sq.base.obj.IsElementary ∧
      CommSq sq.source.obj.toEtale.hom sq.map f sq.base.obj.toEtale.hom ∧
        sq.map sq.source.obj.point = sq.base.obj.point := sorry

end RefinementSquare

end AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary
