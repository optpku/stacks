/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Finite
public import ReasLib.RingTheory.RingHom.IndEtale.BaseChange

@[expose] public section

open CategoryTheory

universe v u

namespace CommAlgCat

namespace IndEtale

/-- The object property of ind-étale `R`-algebras. -/
abbrev indEtale (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ (algebraMap R S).IndEtale

end IndEtale

/-- The full subcategory of ind-étale `R`-algebras. -/
abbrev IndEtale (R : Type u) [CommRing R] : Type _ :=
  (IndEtale.indEtale.{v} R).FullSubcategory

namespace IndEtale

/-- An object of `CommAlgCat` is ind-étale precisely when its structure map is. -/
theorem indEtale_iff {R : Type u} [CommRing R] (S : CommAlgCat.{v} R) :
    indEtale.{v} R S ↔ (algebraMap R S).IndEtale := Iff.rfl

/-- An ind-étale algebra object coerces to its underlying carrier type. -/
instance instCoeSort {R : Type u} [CommRing R] : CoeSort (IndEtale.{v} R) (Type v) :=
  ⟨fun S ↦ S.obj⟩

/-- The defining ind-étaleness property of an object of `CommAlgCat.IndEtale R`. -/
theorem algebraMap_indEtale {R : Type u} [CommRing R] (S : IndEtale.{v} R) :
    (algebraMap R S).IndEtale :=
  S.property

/-- Build an object of `CommAlgCat.IndEtale R` from an ind-étale `R`-algebra. -/
abbrev of (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (h : (algebraMap R S).IndEtale) : IndEtale.{v} R where
  obj := .of R S
  property := h

/-- The underlying `CommAlgCat` object of `IndEtale.of` is the bundled algebra. -/
theorem of_obj (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (h : (algebraMap R S).IndEtale) :
    (of R S h).obj = .of R S := rfl

/-- The property of `IndEtale.of` is the supplied ind-étaleness witness. -/
theorem of_property (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (h : (algebraMap R S).IndEtale) :
    (of R S h).property = h := rfl

/-- Build a morphism of ind-étale algebras from an algebra homomorphism. -/
abbrev ofHom {R : Type u} [CommRing R] {S T : Type v}
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hS : (algebraMap R S).IndEtale) (hT : (algebraMap R T).IndEtale)
    (f : S →ₐ[R] T) :
    of R S hS ⟶ of R T hT where
  hom := CommAlgCat.ofHom f

/-- The underlying morphism of `IndEtale.ofHom` is the bundled algebra map. -/
theorem ofHom_hom {R : Type u} [CommRing R] {S T : Type v}
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hS : (algebraMap R S).IndEtale) (hT : (algebraMap R T).IndEtale)
    (f : S →ₐ[R] T) :
    (ofHom hS hT f).hom = CommAlgCat.ofHom f := rfl

/-- Construct an isomorphism of ind-étale algebras from an algebra equivalence. -/
abbrev isoMk {R : Type u} [CommRing R] {S T : IndEtale.{v} R} (e : S.obj ≃ₐ[R] T.obj) :
    S ≅ T :=
  ObjectProperty.isoMk _ (CommAlgCat.isoMk e)

/-- `IndEtale.isoMk` is the full-subcategory isomorphism induced by an algebra equivalence. -/
theorem isoMk_eq {R : Type u} [CommRing R] {S T : IndEtale.{v} R} (e : S.obj ≃ₐ[R] T.obj) :
    isoMk e = ObjectProperty.isoMk _ (CommAlgCat.isoMk e) := rfl

end IndEtale

end CommAlgCat
