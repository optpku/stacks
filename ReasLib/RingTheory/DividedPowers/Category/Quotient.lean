module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.DividedPowers.Category
public import ReasLib.RingTheory.RingHom.Quotient

@[expose] public section

/-!
# Quotients of Divided Power Rings

This module packages quotienting by the distinguished divided-power ideal as a functor to
commutative rings.
-/

open CategoryTheory

universe u

namespace DividedPowerRing

/-- The ring homomorphism on distinguished-ideal quotients induced by a divided-power ring morphism. -/
@[stacks 0H86 "quotient map"]
def quotientMap {A B : DividedPowerRing.{u}} (f : A ⟶ B) :
    A ⧸ A.ideal →+* B ⧸ B.ideal :=
  f.toRingHom.quotientByIdeals A.ideal B.ideal f.ideal_comp

/-- The quotient map sends the class of an element to the class of its image. -/
@[simp]
theorem quotientMap_mk {A B : DividedPowerRing.{u}} (f : A ⟶ B) (a : A) :
    quotientMap f (Ideal.Quotient.mk A.ideal a) =
      Ideal.Quotient.mk B.ideal (f.toRingHom a) := sorry

/-- The quotient map of an identity is the categorical identity. -/
theorem quotientMap_id (A : DividedPowerRing.{u}) :
    CommRingCat.ofHom (quotientMap (𝟙 A)) =
      𝟙 (CommRingCat.of (A ⧸ A.ideal)) := sorry

/-- Quotient maps preserve composition of divided-power ring morphisms. -/
theorem quotientMap_comp {A B C : DividedPowerRing.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    CommRingCat.ofHom (quotientMap (f ≫ g)) =
      CommRingCat.ofHom (quotientMap f) ≫ CommRingCat.ofHom (quotientMap g) := sorry

/-- The functor sending a divided-power ring to the quotient by its distinguished divided-power ideal. -/
@[stacks 0H86 "infrastructure: quotient functor for divided-power rings"]
def quotient : DividedPowerRing.{u} ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of (A ⧸ A.ideal)
  map f := CommRingCat.ofHom (quotientMap f)
  map_id A := quotientMap_id A
  map_comp f g := quotientMap_comp f g

/-- The quotient functor sends a divided-power ring to its distinguished-ideal quotient. -/
@[simp]
theorem quotient_obj (A : DividedPowerRing.{u}) :
    quotient.obj A = CommRingCat.of (A ⧸ A.ideal) := sorry

/-- The quotient functor maps a morphism by its induced quotient ring homomorphism. -/
@[simp]
theorem quotient_map {A B : DividedPowerRing.{u}} (f : A ⟶ B) :
    quotient.map f = CommRingCat.ofHom (quotientMap f) := sorry

/-- The map of the quotient functor sends a residue class to the class of its image. -/
@[simp]
theorem quotient_map_mk {A B : DividedPowerRing.{u}} (f : A ⟶ B) (a : A) :
    quotient.map f (Ideal.Quotient.mk A.ideal a) =
      Ideal.Quotient.mk B.ideal (f.toRingHom a) := sorry

end DividedPowerRing
