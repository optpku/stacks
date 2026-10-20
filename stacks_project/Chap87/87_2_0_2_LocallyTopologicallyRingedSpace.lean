module

public import Mathlib.Topology.Category.TopCat.OpenNhds
public import stacks_project.Chap87.«87_2_0_1_LocallyTopologicallyRingedSpace»

/-!
# The category of locally topologically ringed spaces

This module equips `LocallyTopologicallyRingedSpace` with its category structure, open
restrictions, and the forgetful functor to sheafed spaces of topological rings.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory TopCat Topology TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

/-- The category of locally topologically ringed spaces. Morphisms are morphisms of sheaves of
topological rings that are local on underlying stalks. -/
instance : Category LocallyTopologicallyRingedSpace.{u} where
  Hom := Hom
  id := id
  comp f g := comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The forgetful functor from locally topologically ringed spaces to sheafed spaces of
topological rings. -/
def forgetToSheafedSpace :
    LocallyTopologicallyRingedSpace.{u} ⥤ SheafedSpace TopCommRingCat.{u} where
  obj X := X.toSheafedSpace
  map f := f.toSheafedHom
  map_id := sorry
  map_comp := sorry

/-- Restriction of a locally topologically ringed space along an open embedding. -/
def restrict {U : TopCat.{u}} (X : LocallyTopologicallyRingedSpace.{u})
    {f : U ⟶ X.carrier} (h : IsOpenEmbedding f) : LocallyTopologicallyRingedSpace.{u} where
  toSheafedSpace := X.toSheafedSpace.restrict h
  isLocalRing := sorry

end AlgebraicGeometry.LocallyTopologicallyRingedSpace
