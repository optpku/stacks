/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- Flatten a full subcategory cut out inside a larger full subcategory. -/
def flattenFunctor (P Q : ObjectProperty C) (_ : P ≤ Q) :
    (P.inverseImage Q.ι).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((P.inverseImage Q.ι).ι ⋙ Q.ι) (fun X ↦ X.property)

/-- Regard an object of a smaller full subcategory as an object of the corresponding
nested full subcategory. -/
def nestedFunctor (P Q : ObjectProperty C) (h : P ≤ Q) :
    P.FullSubcategory ⥤ (P.inverseImage Q.ι).FullSubcategory :=
  (P.inverseImage Q.ι).lift (Q.lift P.ι (fun X ↦ h X.obj X.property))
    (fun X ↦ X.property)

/-- Component of the unit for flattening a nested full subcategory. -/
def nestedUnitApp (P Q : ObjectProperty C) (h : P ≤ Q)
    (X : (P.inverseImage Q.ι).FullSubcategory) :
    X ≅ (flattenFunctor P Q h ⋙ nestedFunctor P Q h).obj X :=
  (P.inverseImage Q.ι).isoMk (Q.isoMk (Iso.refl X.obj.obj))

/-- Naturality of the unit for flattening a nested full subcategory. -/
theorem nestedUnitApp_naturality (P Q : ObjectProperty C) (h : P ≤ Q)
    {X Y : (P.inverseImage Q.ι).FullSubcategory} (f : X ⟶ Y) :
    f ≫ (nestedUnitApp P Q h Y).hom =
      (nestedUnitApp P Q h X).hom ≫
        (flattenFunctor P Q h ⋙ nestedFunctor P Q h).map f := sorry

/-- Unit for flattening a nested full subcategory. -/
def nestedUnitIso (P Q : ObjectProperty C) (h : P ≤ Q) :
    𝟭 (P.inverseImage Q.ι).FullSubcategory ≅
      flattenFunctor P Q h ⋙ nestedFunctor P Q h :=
  NatIso.ofComponents (nestedUnitApp P Q h)
    (fun f ↦ nestedUnitApp_naturality P Q h f)

/-- Component of the counit for flattening a nested full subcategory. -/
def nestedCounitApp (P Q : ObjectProperty C) (h : P ≤ Q)
    (X : P.FullSubcategory) :
    (nestedFunctor P Q h ⋙ flattenFunctor P Q h).obj X ≅ X :=
  P.isoMk (Iso.refl X.obj)

/-- Naturality of the counit for flattening a nested full subcategory. -/
theorem nestedCounitApp_naturality (P Q : ObjectProperty C) (h : P ≤ Q)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    (nestedFunctor P Q h ⋙ flattenFunctor P Q h).map f ≫
        (nestedCounitApp P Q h Y).hom =
      (nestedCounitApp P Q h X).hom ≫ f := sorry

/-- Counit for flattening a nested full subcategory. -/
def nestedCounitIso (P Q : ObjectProperty C) (h : P ≤ Q) :
    nestedFunctor P Q h ⋙ flattenFunctor P Q h ≅ 𝟭 P.FullSubcategory :=
  NatIso.ofComponents (nestedCounitApp P Q h)
    (fun f ↦ nestedCounitApp_naturality P Q h f)

/-- Triangle identity for flattening a nested full subcategory. -/
theorem nestedTriangle (P Q : ObjectProperty C) (h : P ≤ Q)
    (X : (P.inverseImage Q.ι).FullSubcategory) :
    (flattenFunctor P Q h).map ((nestedUnitIso P Q h).hom.app X) ≫
        (nestedCounitIso P Q h).hom.app ((flattenFunctor P Q h).obj X) =
      𝟙 ((flattenFunctor P Q h).obj X) := sorry

/-- A nested full subcategory defined by `P` inside a property `Q` containing it is
canonically equivalent to the full subcategory defined directly by `P`. -/
def nestedEquivalence (P Q : ObjectProperty C) (h : P ≤ Q) :
    (P.inverseImage Q.ι).FullSubcategory ≌ P.FullSubcategory where
  functor := flattenFunctor P Q h
  inverse := nestedFunctor P Q h
  unitIso := nestedUnitIso P Q h
  counitIso := nestedCounitIso P Q h
  functor_unitIso_comp := nestedTriangle P Q h

end CategoryTheory.ObjectProperty
