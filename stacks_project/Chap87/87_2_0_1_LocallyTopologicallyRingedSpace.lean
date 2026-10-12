/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Category.TopCommRingCat

/-!
# Locally topologically ringed spaces

A locally topologically ringed space is a topological space equipped with a sheaf of topological
commutative rings whose underlying stalks are local rings. Morphisms are morphisms of sheafed
spaces that are local on underlying stalks.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Functor Opposite Topology TopologicalSpace

namespace AlgebraicGeometry

/-- Forget the topology on the values of a sheaf of topological commutative rings. -/
def SheafedSpace.underlyingRingPresheaf (X : SheafedSpace TopCommRingCat.{u}) :
    X.carrier.Presheaf CommRingCat.{u} :=
  X.presheaf ⋙ forget₂ TopCommRingCat CommRingCat

/-- The underlying stalk map of a morphism of sheaves of topological commutative rings. -/
noncomputable def SheafedSpace.underlyingStalkRingHom {X Y : SheafedSpace TopCommRingCat.{u}}
    (f : X ⟶ Y) (x : X.carrier) :
    (Y.underlyingRingPresheaf.stalk (f.hom.base x)) →+*
      (X.underlyingRingPresheaf.stalk x) :=
  (((forget₂ TopCommRingCat CommRingCat).mapPresheaf.map f.hom).stalkMap x).hom

/-- A topological space with a sheaf of topological commutative rings whose underlying stalks are
local rings. -/
structure LocallyTopologicallyRingedSpace extends SheafedSpace TopCommRingCat.{u} where
  /-- Underlying stalks are local rings. -/
  isLocalRing : ∀ x,
    IsLocalRing
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).obj
        (presheaf ⋙ forget₂ TopCommRingCat CommRingCat))

namespace LocallyTopologicallyRingedSpace

/-- Reassemble a locally topologically ringed space from a sheaf of topological rings with local
underlying stalks. -/
def ofSheafedSpace (X : SheafedSpace TopCommRingCat.{u})
    (h : ∀ x, IsLocalRing (X.underlyingRingPresheaf.stalk x)) :
    LocallyTopologicallyRingedSpace.{u} where
  toSheafedSpace := X
  isLocalRing := h

/-- The underlying ring-valued presheaf of a locally topologically ringed space. -/
def underlyingRingPresheaf (X : LocallyTopologicallyRingedSpace.{u}) :
    X.carrier.Presheaf CommRingCat.{u} :=
  X.toSheafedSpace.underlyingRingPresheaf

/-- A morphism of locally topologically ringed spaces is a morphism of the underlying sheafed
spaces which is a local homomorphism on underlying stalks. -/
structure Hom (X Y : LocallyTopologicallyRingedSpace.{u}) where
  /-- Underlying morphism of sheaves of topological rings. -/
  toSheafedHom : X.toSheafedSpace ⟶ Y.toSheafedSpace
  /-- The induced maps on underlying stalks are local homomorphisms. -/
  isLocalHom : ∀ x : X.carrier, IsLocalHom (SheafedSpace.underlyingStalkRingHom toSheafedHom x)

/-- The identity morphism of a locally topologically ringed space. -/
def id (X : LocallyTopologicallyRingedSpace.{u}) : Hom X X where
  toSheafedHom := 𝟙 X.toSheafedSpace
  isLocalHom := fun _ ↦ sorry

/-- Composition of morphisms of locally topologically ringed spaces. -/
def comp {X Y Z : LocallyTopologicallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z where
  toSheafedHom := f.toSheafedHom ≫ g.toSheafedHom
  isLocalHom := fun _ ↦ sorry

/-- The underlying stalk map of a morphism of locally topologically ringed spaces. -/
noncomputable def Hom.stalkMap {X Y : LocallyTopologicallyRingedSpace.{u}} (f : Hom X Y)
    (x : X.carrier) :
    Y.underlyingRingPresheaf.stalk (f.toSheafedHom.hom.base x) ⟶
      X.underlyingRingPresheaf.stalk x :=
  ((forget₂ TopCommRingCat CommRingCat).mapPresheaf.map f.toSheafedHom.hom).stalkMap x

end LocallyTopologicallyRingedSpace

end AlgebraicGeometry
