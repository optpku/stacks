/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.FiniteComponents

/-!
# Rational maps preserving generic points of components

This file defines rational maps that carry the generic points of the source
components exactly onto the generic points of the target components.  For
schemes with finitely many irreducible components on quasi-compact opens,
these maps have a composition without an irreducibility assumption.
-/

@[expose] public section

open CategoryTheory hiding Quotient
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {W X Y Z : Scheme.{u}}

namespace PartialMap

/-- A partial map preserves generic points of components when the image of
the generic points of its domain is exactly the set of generic points of its
target. -/
def MapsGenericPoints (f : X.PartialMap Y) : Prop :=
  f.hom.base '' genericPoints f.domain = genericPoints Y

/-- The generic-point-preserving condition on a partial map is exact equality
of the corresponding generic-point image and target. -/
theorem mapsGenericPoints_iff (f : X.PartialMap Y) :
    f.MapsGenericPoints ↔
      f.hom.base '' genericPoints f.domain = genericPoints Y := sorry

/-- Equivalent partial maps from a scheme with finite irreducible components
on quasi-compact opens preserve generic points simultaneously. -/
theorem mapsGenericPoints_iff_of_equiv
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {f g : X.PartialMap Y} (h : f.equiv g) :
    f.MapsGenericPoints ↔ g.MapsGenericPoints := sorry

/-- The inverse image of the domain of a second partial map is dense in the
source whenever the first partial map preserves generic points. -/
theorem dense_compDomain_of_mapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (hf : f.MapsGenericPoints) :
    Dense ((f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain) : X.Opens) : Set X) := sorry

/-- The identity partial map preserves the generic points of components. -/
theorem mapsGenericPoints_id (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (PartialMap.id X).MapsGenericPoints := sorry

/-- Composition of generic-point-preserving partial maps, defined on the
ambient image of the inverse image of the second map's domain. -/
noncomputable def compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (hf : f.MapsGenericPoints) : X.PartialMap Z where
  domain := f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)
  dense_domain := dense_compDomain_of_mapsGenericPoints f g hf
  hom := (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
    f.hom ∣_ g.domain ≫ g.hom

/-- Composition of partial maps preserving generic points again preserves
generic points. -/
theorem mapsGenericPoints_compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (hf : f.MapsGenericPoints) (hg : g.MapsGenericPoints) :
    (compOfMapsGenericPoints f g hf).MapsGenericPoints := sorry

/-- Composition of generic-point-preserving partial maps respects equivalence
in both arguments. -/
theorem compOfMapsGenericPoints_equiv
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    {f₁ f₂ : X.PartialMap Y} {g₁ g₂ : Y.PartialMap Z}
    (hf₁ : f₁.MapsGenericPoints) (hf₂ : f₂.MapsGenericPoints)
    (hfg : f₁.equiv f₂) (hg : g₁.equiv g₂) :
    (compOfMapsGenericPoints f₁ g₁ hf₁).equiv
      (compOfMapsGenericPoints f₂ g₂ hf₂) := sorry

/-- Composing the identity partial map on the source with a partial map is
equivalent to that partial map. -/
theorem id_compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (f : X.PartialMap Y) :
    (compOfMapsGenericPoints (PartialMap.id X) f
      (mapsGenericPoints_id X)).equiv f := sorry

/-- Composing a generic-point-preserving partial map with the identity on its
target is equivalent to the original partial map. -/
theorem compOfMapsGenericPoints_id
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (hf : f.MapsGenericPoints) :
    (compOfMapsGenericPoints f (PartialMap.id Y) hf).equiv f := sorry

/-- Composition of generic-point-preserving partial maps is associative up to
partial-map equivalence. -/
theorem compOfMapsGenericPoints_assoc
    [HasFiniteIrreducibleComponentsOnCompactOpens W]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : W.PartialMap X) (g : X.PartialMap Y) (h : Y.PartialMap Z)
    (hf : f.MapsGenericPoints) (hg : g.MapsGenericPoints) :
    (compOfMapsGenericPoints
      (compOfMapsGenericPoints f g hf) h
      (mapsGenericPoints_compOfMapsGenericPoints f g hf hg)).equiv
        (compOfMapsGenericPoints f
          (compOfMapsGenericPoints g h hg) hf) := sorry

end PartialMap

namespace RationalMap

/-- A rational map preserves generic points of components when one of its
partial-map representatives does so. -/
def MapsGenericPoints (f : X ⤏ Y) : Prop :=
  ∃ g : X.PartialMap Y, g.MapsGenericPoints ∧ g.toRationalMap = f

/-- A rational map preserves generic points exactly when it has a
generic-point-preserving partial-map representative. -/
theorem mapsGenericPoints_iff_exists_partialMap (f : X ⤏ Y) :
    f.MapsGenericPoints ↔
      ∃ g : X.PartialMap Y, g.MapsGenericPoints ∧ g.toRationalMap = f := sorry

/-- For a source with finite irreducible components on quasi-compact opens, a
rational map preserves generic points exactly when its canonical
representative does. -/
theorem mapsGenericPoints_iff_representative
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (f : X ⤏ Y) :
    f.MapsGenericPoints ↔ f.representative.MapsGenericPoints := sorry

/-- The identity rational map preserves the generic points of components. -/
theorem mapsGenericPoints_id (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (RationalMap.id X).MapsGenericPoints := sorry

/-- Composition of rational maps preserving generic points, obtained from the
canonical representatives and explicit partial-map composition. -/
noncomputable def compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X ⤏ Y) (g : Y ⤏ Z) (hf : f.MapsGenericPoints) : X ⤏ Z :=
  (PartialMap.compOfMapsGenericPoints f.representative g.representative
    ((mapsGenericPoints_iff_representative f).mp hf)).toRationalMap

/-- Composition of rational maps preserving generic points again preserves
generic points. -/
theorem mapsGenericPoints_compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X ⤏ Y) (g : Y ⤏ Z)
    (hf : f.MapsGenericPoints) (hg : g.MapsGenericPoints) :
    (compOfMapsGenericPoints f g hf).MapsGenericPoints := sorry

end RationalMap

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Schemes whose quasi-compact open subschemes have finitely many
irreducible components. -/
def FiniteComponentRationalMapCat :=
  { X : Scheme.{u} // Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X }

namespace FiniteComponentRationalMapCat

/-- An object of the finite-component rational-map category carries the
canonical finiteness instance on its underlying scheme. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens
    (X : FiniteComponentRationalMapCat.{u}) :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X.1 :=
  X.2

/-- A morphism between finite-component schemes is a rational map preserving
the generic points of components. -/
def Hom (X Y : FiniteComponentRationalMapCat.{u}) :=
  { f : X.1 ⤏ Y.1 // f.MapsGenericPoints }

namespace Hom

/-- The identity morphism of a finite-component scheme. -/
def id (X : FiniteComponentRationalMapCat.{u}) : Hom X X :=
  ⟨Scheme.RationalMap.id X.1, Scheme.RationalMap.mapsGenericPoints_id X.1⟩

/-- Composition of morphisms between finite-component schemes. -/
noncomputable def comp {X Y Z : FiniteComponentRationalMapCat.{u}}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨Scheme.RationalMap.compOfMapsGenericPoints f.1 g.1 f.2,
    Scheme.RationalMap.mapsGenericPoints_compOfMapsGenericPoints
      f.1 g.1 f.2 g.2⟩

/-- The identity morphism on the source is a left identity for composition. -/
theorem id_comp {X Y : FiniteComponentRationalMapCat.{u}} (f : Hom X Y) :
    comp (id X) f = f := sorry

/-- The identity morphism on the target is a right identity for composition. -/
theorem comp_id {X Y : FiniteComponentRationalMapCat.{u}} (f : Hom X Y) :
    comp f (id Y) = f := sorry

/-- Composition of finite-component rational maps is associative. -/
theorem comp_assoc {W X Y Z : FiniteComponentRationalMapCat.{u}}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- The category of finite-component schemes and rational maps preserving
generic points of components. -/
noncomputable instance instCategory :
    CategoryTheory.Category.{u} FiniteComponentRationalMapCat.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end FiniteComponentRationalMapCat

end AlgebraicGeometry
