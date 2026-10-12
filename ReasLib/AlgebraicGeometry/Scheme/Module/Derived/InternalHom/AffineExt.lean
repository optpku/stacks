/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor
public import ReasLib.RingTheory.Localization.BasicOpen
public import ReasLib.Topology.Sheaves.Basis.Comparison
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Localized Ext on an affine scheme

This file constructs the presheaf of shifted derived morphisms after localization on
principal opens and its associated sheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

/-- Ring elements regarded as a presentation of the principal-open basis, ordered by inclusion
of their associated principal opens. -/
def PrincipalOpenIndex (A : Type u) := A

namespace PrincipalOpenIndex

/-- A ring element as an object of the presented principal-open basis. -/
def of {A : Type u} (f : A) : PrincipalOpenIndex A := f

/-- The ring element presenting a principal-open basis object. -/
def element {A : Type u} (f : PrincipalOpenIndex A) : A := f

/-- The principal open presented by a ring element is contained in itself. -/
theorem basicOpen_le_self {A : Type u} [CommRing A]
    (f : PrincipalOpenIndex A) :
    PrimeSpectrum.basicOpen f.element ≤ PrimeSpectrum.basicOpen f.element := sorry

/-- Inclusions between principal opens presented by ring elements are transitive. -/
theorem basicOpen_le_trans {A : Type u} [CommRing A]
    (f g q : PrincipalOpenIndex A)
    (hfg : PrimeSpectrum.basicOpen f.element ≤ PrimeSpectrum.basicOpen g.element)
    (hgq : PrimeSpectrum.basicOpen g.element ≤ PrimeSpectrum.basicOpen q.element) :
    PrimeSpectrum.basicOpen f.element ≤ PrimeSpectrum.basicOpen q.element := sorry

/-- The canonical preorder on ring-element presentations induced by inclusion of principal
opens. -/
noncomputable instance instPreorder {A : Type u} [CommRing A] :
    Preorder (PrincipalOpenIndex A) where
  le f g := PrimeSpectrum.basicOpen f.element ≤ PrimeSpectrum.basicOpen g.element
  le_refl := basicOpen_le_self
  le_trans := basicOpen_le_trans

end PrincipalOpenIndex

/-- The morphism of opens induced by a morphism in the presented principal-open basis. -/
noncomputable def principalOpenMap {A : Type u} [CommRing A]
    {f g : PrincipalOpenIndex A} (i : f ⟶ g) :
    PrimeSpectrum.basicOpen f.element ⟶ PrimeSpectrum.basicOpen g.element :=
  homOfLE (leOfHom i)

/-- The principal-open map attached to an identity is an identity. -/
theorem principalOpenMap_id (A : Type u) [CommRing A]
    (f : PrincipalOpenIndex A) :
    principalOpenMap (𝟙 f) = 𝟙 (PrimeSpectrum.basicOpen f.element) := sorry

/-- Principal-open maps preserve composition. -/
theorem principalOpenMap_comp (A : Type u) [CommRing A]
    {f g q : PrincipalOpenIndex A} (i : f ⟶ g) (j : g ⟶ q) :
    principalOpenMap (i ≫ j) = principalOpenMap i ≫ principalOpenMap j := sorry

/-- The inclusion of the presented principal-open basis into all opens of `Spec(A)`. -/
noncomputable def principalOpenFunctor (A : Type u) [CommRing A] :
    PrincipalOpenIndex A ⥤ Opens (PrimeSpectrum A) where
  obj f := PrimeSpectrum.basicOpen f.element
  map i := principalOpenMap i
  map_id := principalOpenMap_id A
  map_comp := principalOpenMap_comp A

/-- The opens in the image of `principalOpenFunctor` form the standard basis of `Spec(A)`. -/
theorem principalOpenFunctor_isBasis (A : Type u) [CommRing A] :
    Opens.IsBasis (Set.range fun f : PrincipalOpenIndex A ↦
      (principalOpenFunctor A).obj f) := sorry

/-- The localized `Ext^n` group attached to the principal open `D(f)`. -/
noncomputable abbrev affineExtValue {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (f : A) :
    AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of
    (ShiftedHom
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (Localization.Away f))).obj K)
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (Localization.Away f))).obj L) n)

/-- Iterated derived scalar extension along `A ⟶ A_f ⟶ A_g` agrees with direct
extension along `A ⟶ A_g`. -/
noncomputable abbrev affineExtBaseChangeIso {A : Type u} [CommRing A]
    (f g : A) (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ModuleCat.derivedExtensionOfScalars (algebraMap A (Localization.Away f)) ⋙
        ModuleCat.derivedExtensionOfScalars
          (PrimeSpectrum.awayToAwayRingHom f g h) ≅
      ModuleCat.derivedExtensionOfScalars (algebraMap A (Localization.Away g)) :=
  ModuleCat.derivedExtensionOfScalarsCompIso
    (algebraMap A (Localization.Away f))
    (PrimeSpectrum.awayToAwayRingHom f g h)
    (algebraMap A (Localization.Away g))
    (PrimeSpectrum.awayToAwayAlgHom f g h).comp_algebraMap

/-- The canonical restriction function on localized shifted Hom groups along `D(g) ⊆ D(f)`. -/
noncomputable def affineExtRestrictionFunction {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) {f g : A}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    affineExtValue K L n f → affineExtValue K L n g :=
  (ModuleCat.derivedExtensionOfScalars
      (PrimeSpectrum.awayToAwayRingHom f g h)).shiftedHomMap
    ((affineExtBaseChangeIso f g h).app K)
    ((affineExtBaseChangeIso f g h).app L) n

/-- Canonical affine-Ext restriction preserves zero. -/
theorem affineExtRestrictionFunction_map_zero {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) {f g : A}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    affineExtRestrictionFunction K L n h 0 = 0 := sorry

/-- Canonical affine-Ext restriction preserves addition. -/
theorem affineExtRestrictionFunction_map_add {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) {f g : A}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (x y : affineExtValue K L n f) :
    affineExtRestrictionFunction K L n h (x + y) =
      affineExtRestrictionFunction K L n h x +
        affineExtRestrictionFunction K L n h y := sorry

/-- Restriction in localized affine `Ext` along an inclusion of principal opens. -/
noncomputable def affineExtRestriction {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) {f g : A}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    affineExtValue K L n f ⟶ affineExtValue K L n g :=
  AddCommGrpCat.ofHom
    { toFun := affineExtRestrictionFunction K L n h
      map_zero' := affineExtRestrictionFunction_map_zero K L n h
      map_add' := affineExtRestrictionFunction_map_add K L n h }

/-- Restriction on affine `Ext` is the identity for an identity inclusion. -/
theorem affineExtRestriction_id {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (f : A) :
    affineExtRestriction K L n
      (leOfHom (𝟙 (PrincipalOpenIndex.of f))) = 𝟙 _ := sorry

/-- Affine `Ext` restrictions compose along nested principal opens. -/
theorem affineExtRestriction_comp {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    {f g q : PrincipalOpenIndex A} (i : g ⟶ f) (j : q ⟶ g) :
    affineExtRestriction K L n (leOfHom (j ≫ i)) =
      affineExtRestriction K L n (leOfHom i) ≫
        affineExtRestriction K L n (leOfHom j) := sorry

/-- The localized-Ext presheaf on the presented principal-open basis of `Spec(A)`. -/
noncomputable def affineExtBasisPresheaf {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (PrincipalOpenIndex A)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj f := affineExtValue K L n f.unop.element
  map i := affineExtRestriction K L n (leOfHom i.unop)
  map_id f := affineExtRestriction_id K L n f.unop.element
  map_comp i j := affineExtRestriction_comp K L n i.unop j.unop

/-- On the presentation of `D(f)`, the affine-Ext basis presheaf has value
`Ext^n_{A_f}(K ⊗ᴸ A_f, L ⊗ᴸ A_f)`. -/
theorem affineExtBasisPresheaf_obj {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (f : A) :
    (affineExtBasisPresheaf K L n).obj (op (PrincipalOpenIndex.of f)) =
      affineExtValue K L n f := sorry

/-- The map of the affine-Ext basis presheaf along `D(g) ⊆ D(f)` is the canonical derived
localization/base-change restriction. -/
theorem affineExtBasisPresheaf_map {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    {f g : PrincipalOpenIndex A} (i : g ⟶ f) :
    (affineExtBasisPresheaf K L n).map i.op =
      affineExtRestriction K L n (leOfHom i) := sorry

/-- The presheaf on all opens obtained by right Kan extending localized affine `Ext` from the
principal-open basis. -/
noncomputable abbrev affineExtPresheaf {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (Opens (PrimeSpectrum A))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (principalOpenFunctor A).op.ran.obj (affineExtBasisPresheaf K L n)

/-- The sheaf associated to the localized affine-Ext presheaf. -/
noncomputable abbrev affineExtSheaf {A : Type u} [CommRing A]
    [HasWeakSheafify (Opens.grothendieckTopology (PrimeSpectrum A))
      AddCommGrpCat.{u + 1}]
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Opens.grothendieckTopology (PrimeSpectrum A))
    AddCommGrpCat.{u + 1}).obj (affineExtPresheaf K L n)

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
