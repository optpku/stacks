/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Topology.Category.TopCat.OpenNhds

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry

namespace LocallyTopologicallyRingedSpaceCat

/-- The ring-valued presheaf obtained by forgetting the topology of sections. -/
def ringPresheaf (X : SheafedSpace TopCommRingCat.{u}) :
    X.carrier.Presheaf CommRingCat.{u} :=
  X.presheaf ⋙ forget₂ TopCommRingCat CommRingCat

/-- The ring homomorphism on stalks induced by a morphism of sheafed spaces. -/
noncomputable def stalkRingHom {X Y : SheafedSpace TopCommRingCat.{u}}
    (f : X ⟶ Y) (x : X.carrier) :
    (ringPresheaf Y).stalk (f.hom.base x) →+* (ringPresheaf X).stalk x :=
  (((forget₂ TopCommRingCat CommRingCat).mapPresheaf.map f.hom).stalkMap x).hom

end LocallyTopologicallyRingedSpaceCat

/-- Sheafed spaces of topological commutative rings whose underlying ring stalks are local. -/
def LocallyTopologicallyRingedSpaceCat :=
  {X : SheafedSpace TopCommRingCat.{u} //
    ∀ x : X.carrier, IsLocalRing ((LocallyTopologicallyRingedSpaceCat.ringPresheaf X).stalk x)}

namespace LocallyTopologicallyRingedSpaceCat

/-- The underlying sheafed space of a locally topologically ringed space. -/
def toSheafedSpace (X : LocallyTopologicallyRingedSpaceCat.{u}) :
    SheafedSpace TopCommRingCat.{u} := X.val

/-- The underlying topological space. -/
def carrier (X : LocallyTopologicallyRingedSpaceCat.{u}) : TopCat.{u} :=
  X.toSheafedSpace.carrier

/-- Construct a locally topologically ringed space from a sheaf with local ring stalks. -/
def ofSheafedSpace (X : SheafedSpace TopCommRingCat.{u})
    (h : ∀ x : X.carrier, IsLocalRing ((ringPresheaf X).stalk x)) :
    LocallyTopologicallyRingedSpaceCat.{u} := ⟨X, h⟩

/-- The constructor retains the underlying sheaf and its local ring stalks. -/
theorem ofSheafedSpace_spec (X : SheafedSpace TopCommRingCat.{u})
    (h : ∀ x : X.carrier, IsLocalRing ((ringPresheaf X).stalk x)) :
    (ofSheafedSpace X h).toSheafedSpace = X ∧
      ∀ x : X.carrier, IsLocalRing ((ringPresheaf X).stalk x) := sorry

/-- The ring-valued presheaf of a locally topologically ringed space. -/
def underlyingRingPresheaf (X : LocallyTopologicallyRingedSpaceCat.{u}) :
    X.carrier.Presheaf CommRingCat.{u} := ringPresheaf X.toSheafedSpace

/-- Morphisms of sheafed spaces whose underlying stalk homomorphisms are local. -/
def Hom (X Y : LocallyTopologicallyRingedSpaceCat.{u}) :=
  {f : X.toSheafedSpace ⟶ Y.toSheafedSpace //
    ∀ x : X.carrier, IsLocalHom (stalkRingHom f x)}

/-- The underlying morphism of sheafed spaces. -/
def Hom.toSheafedHom {X Y : LocallyTopologicallyRingedSpaceCat.{u}} (f : Hom X Y) :
    X.toSheafedSpace ⟶ Y.toSheafedSpace := f.val

/-- Construct a local morphism from a sheafed-space morphism local on stalks. -/
def Hom.ofSheafedHom {X Y : LocallyTopologicallyRingedSpaceCat.{u}}
    (f : X.toSheafedSpace ⟶ Y.toSheafedSpace)
    (h : ∀ x : X.carrier, IsLocalHom (stalkRingHom f x)) : Hom X Y := ⟨f, h⟩

/-- The morphism constructor retains the sheaf morphism and its locality on stalks. -/
theorem Hom.ofSheafedHom_spec {X Y : LocallyTopologicallyRingedSpaceCat.{u}}
    (f : X.toSheafedSpace ⟶ Y.toSheafedSpace)
    (h : ∀ x : X.carrier, IsLocalHom (stalkRingHom f x)) :
    (Hom.ofSheafedHom f h).toSheafedHom = f ∧
      ∀ x : X.carrier, IsLocalHom (stalkRingHom f x) := sorry

/-- The identity morphism is local on stalks. -/
theorem id_isLocalHom (X : LocallyTopologicallyRingedSpaceCat.{u}) :
    ∀ x : X.carrier, IsLocalHom (stalkRingHom (𝟙 X.toSheafedSpace) x) := sorry

/-- Composition of local sheaf morphisms is local on stalks. -/
theorem comp_isLocalHom {X Y Z : LocallyTopologicallyRingedSpaceCat.{u}}
    (f : Hom X Y) (g : Hom Y Z) :
    ∀ x : X.carrier, IsLocalHom (stalkRingHom (f.toSheafedHom ≫ g.toSheafedHom) x) := sorry

/-- The identity local morphism. -/
def id (X : LocallyTopologicallyRingedSpaceCat.{u}) : Hom X X :=
  Hom.ofSheafedHom (𝟙 X.toSheafedSpace) (id_isLocalHom X)

/-- Composition of local morphisms, with the underlying sheaf morphisms composed. -/
def comp {X Y Z : LocallyTopologicallyRingedSpaceCat.{u}} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z :=
  Hom.ofSheafedHom (f.toSheafedHom ≫ g.toSheafedHom) (comp_isLocalHom f g)

/-- Left identity for composition of local morphisms. -/
theorem id_comp {X Y : LocallyTopologicallyRingedSpaceCat.{u}} (f : Hom X Y) :
    comp (id X) f = f := sorry

/-- Right identity for composition of local morphisms. -/
theorem comp_id {X Y : LocallyTopologicallyRingedSpaceCat.{u}} (f : Hom X Y) :
    comp f (id Y) = f := sorry

/-- Associativity of composition of local morphisms. -/
theorem assoc {W X Y Z : LocallyTopologicallyRingedSpaceCat.{u}}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- The category of locally topologically ringed spaces and local sheaf morphisms. -/
instance instCategory : Category LocallyTopologicallyRingedSpaceCat.{u} where
  Hom := Hom
  id := id
  comp := comp
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc

/-- Forgetting locality retains the supplied sheafed space and its morphisms. -/
def forgetToSheafedSpace :
    LocallyTopologicallyRingedSpaceCat.{u} ⥤ SheafedSpace TopCommRingCat.{u} where
  obj := toSheafedSpace
  map := Hom.toSheafedHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction along an open embedding preserves locality of the underlying ring stalks. -/
theorem restrict_isLocalRing {U : TopCat.{u}} (X : LocallyTopologicallyRingedSpaceCat.{u})
    {f : U ⟶ X.carrier} (h : Topology.IsOpenEmbedding f) :
    ∀ x : U, IsLocalRing ((ringPresheaf (X.toSheafedSpace.restrict h)).stalk x) := sorry

/-- Restriction of a locally topologically ringed space along an open embedding. -/
def restrict {U : TopCat.{u}} (X : LocallyTopologicallyRingedSpaceCat.{u})
    {f : U ⟶ X.carrier} (h : Topology.IsOpenEmbedding f) :
    LocallyTopologicallyRingedSpaceCat.{u} :=
  ofSheafedSpace (X.toSheafedSpace.restrict h) (restrict_isLocalRing X h)

/-- Open restriction retains the restricted sheafed space. -/
theorem restrict_toSheafedSpace {U : TopCat.{u}} (X : LocallyTopologicallyRingedSpaceCat.{u})
    {f : U ⟶ X.carrier} (h : Topology.IsOpenEmbedding f) :
    (X.restrict h).toSheafedSpace = X.toSheafedSpace.restrict h := rfl

/-- The morphism of underlying ring stalks. -/
noncomputable def Hom.stalkMap {X Y : LocallyTopologicallyRingedSpaceCat.{u}} (f : Hom X Y)
    (x : X.carrier) :
    Y.underlyingRingPresheaf.stalk (f.toSheafedHom.hom.base x) ⟶
      X.underlyingRingPresheaf.stalk x :=
  ((forget₂ TopCommRingCat CommRingCat).mapPresheaf.map f.toSheafedHom.hom).stalkMap x

end LocallyTopologicallyRingedSpaceCat

end AlgebraicGeometry
