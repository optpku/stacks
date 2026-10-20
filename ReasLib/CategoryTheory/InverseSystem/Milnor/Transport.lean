/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Milnor

@[expose] public section

/-!
# Transport of Milnor Products

An isomorphism of sequential inverse systems induces an isomorphism of their
underlying product objects.  This leaf records the canonical construction, its
projection formulas, and its compatibility with the Milnor difference map.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem

variable {C : Type u} [Category.{v} C]

/-- The isomorphism of discrete family diagrams underlying an isomorphism of sequential inverse
systems. -/
def familyIso {K L : SequentialInverseSystem C} (e : K ≅ L) :
    Discrete.functor K.family ≅ Discrete.functor L.family :=
  Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)

/-- Existence of the product of a sequential inverse system transports along
an isomorphism of systems. This is an explicit, isomorphism-dependent witness,
not a global instance. -/
noncomputable abbrev hasProductOfIso {K L : SequentialInverseSystem C}
    [HasProduct K.family] (e : K ≅ L) : HasProduct L.family :=
  hasLimit_of_iso (familyIso e)

/-- The component of the hom of the family-diagram isomorphism at stage `n`. -/
@[simp]
theorem familyIso_hom_app {K L : SequentialInverseSystem C} (e : K ≅ L) (n : ℕ) :
    (familyIso e).hom.app (Discrete.mk n) = e.hom.app (op n) := sorry

/-- The component of the inverse of the family-diagram isomorphism at stage `n`. -/
@[simp]
theorem familyIso_inv_app {K L : SequentialInverseSystem C} (e : K ≅ L) (n : ℕ) :
    (familyIso e).inv.app (Discrete.mk n) = e.inv.app (op n) := sorry

/-- The canonical product isomorphism induced by an isomorphism of sequential inverse systems. -/
@[stacks 08TC]
noncomputable def productIso {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    ∏ᶜ K.family ≅ ∏ᶜ L.family :=
  HasLimit.isoOfNatIso (familyIso e)

/-- The hom of `productIso e` is the product map induced by `e.hom`. -/
@[simp]
theorem productIso_hom {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    (productIso e).hom = productMap e.hom := sorry

/-- The inverse of `productIso e` is the product map induced by `e.inv`. -/
@[simp]
theorem productIso_inv {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    (productIso e).inv = productMap e.inv := sorry

/-- The hom of the product isomorphism commutes with every product projection. -/
@[reassoc (attr := simp)]
theorem productIso_hom_comp_π {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) (n : ℕ) :
    (productIso e).hom ≫ Pi.π L.family n = Pi.π K.family n ≫ e.hom.app (op n) := sorry

/-- The inverse of the product isomorphism commutes with every product projection. -/
@[reassoc (attr := simp)]
theorem productIso_inv_comp_π {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) (n : ℕ) :
    (productIso e).inv ≫ Pi.π K.family n = Pi.π L.family n ≫ e.inv.app (op n) := sorry

section

variable [Preadditive C]

/-- The hom of the product isomorphism intertwines the two Milnor difference maps. -/
@[reassoc]
theorem milnorDifferenceMap_comp_productIso_hom {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    K.milnorDifferenceMap ≫ (productIso e).hom =
      (productIso e).hom ≫ L.milnorDifferenceMap := sorry

/-- The inverse of the product isomorphism intertwines the two Milnor difference maps. -/
@[reassoc]
theorem milnorDifferenceMap_comp_productIso_inv {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    L.milnorDifferenceMap ≫ (productIso e).inv =
      (productIso e).inv ≫ K.milnorDifferenceMap := sorry

end

end CategoryTheory.SequentialInverseSystem
