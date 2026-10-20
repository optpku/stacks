/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

@[expose] public section

/-!
# Quotients into Bounded Homotopy Categories

This leaf compares the homotopy quotient with the bounded-below, bounded-above, and bounded
full subcategories. The project-owned bounded-above and bounded quotient functors are restrictions
of the ambient homotopy quotient; their object, morphism, and inclusion computations are exposed
uniformly with Mathlib's bounded-below quotient.
-/

open CategoryTheory
open ComplexShape

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]

namespace HomotopyCategory.Minus

/-- The ambient homotopy quotient carries bounded-above complexes to bounded-above homotopy
objects. -/
@[stacks 013H "bounded-above homotopy quotient preservation"]
theorem quotientMapsTo :
    CochainComplex.minus 𝒜 ≤
      (HomotopyCategory.minus 𝒜).inverseImage
        (HomotopyCategory.quotient 𝒜 (up ℤ)) := sorry

/-- The quotient bridge `Comp⁻(𝒜) ⥤ K⁻(𝒜)`. -/
@[stacks 013H "bounded-above homotopy quotient"]
def quotient : Comp⁻(𝒜) ⥤ HomotopyCategory.Minus 𝒜 :=
  ObjectProperty.FullSubcategory.restrict
    (HomotopyCategory.quotient 𝒜 (up ℤ)) (quotientMapsTo 𝒜)

/-- Forgetting bounded-above structure after the homotopy quotient recovers the ambient
homotopy quotient. -/
@[stacks 013H "bounded-above homotopy quotient inclusion comparison"]
def quotientCompιIso :
    quotient 𝒜 ⋙ ι 𝒜 ≅
      CochainComplex.Minus.ι 𝒜 ⋙ HomotopyCategory.quotient 𝒜 (up ℤ) :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (HomotopyCategory.quotient 𝒜 (up ℤ)) (quotientMapsTo 𝒜)

/-- The bounded-above homotopy quotient retains the object of the ambient homotopy quotient. -/
@[simp]
theorem quotient_obj_obj (K : CochainComplex.Minus 𝒜) :
    ((quotient 𝒜).obj K).obj =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj := sorry

/-- The bounded-above homotopy quotient retains the morphism of the ambient homotopy quotient. -/
@[simp]
theorem quotient_map_hom {K L : CochainComplex.Minus 𝒜} (f : K ⟶ L) :
    ((quotient 𝒜).map f).hom =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map f.hom := sorry

/-- The forward bounded-above quotient inclusion comparison is componentwise the identity. -/
@[simp]
theorem quotientCompιIso_hom_app (K : CochainComplex.Minus 𝒜) :
    (quotientCompιIso 𝒜).hom.app K =
      𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj) := sorry

/-- The inverse bounded-above quotient inclusion comparison is componentwise the identity. -/
@[simp]
theorem quotientCompιIso_inv_app (K : CochainComplex.Minus 𝒜) :
    (quotientCompιIso 𝒜).inv.app K =
      𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj) := sorry

end HomotopyCategory.Minus

namespace HomotopyCategory.Bounded

/-- The ambient homotopy quotient carries bounded complexes to bounded homotopy objects. -/
@[stacks 013H "bounded homotopy quotient preservation"]
theorem quotientMapsTo :
    CochainComplex.bounded 𝒜 ≤
      (HomotopyCategory.bounded 𝒜).inverseImage
        (HomotopyCategory.quotient 𝒜 (up ℤ)) := sorry

/-- The quotient bridge `Compᵇ(𝒜) ⥤ Kᵇ(𝒜)`. -/
@[stacks 013H "bounded homotopy quotient"]
def quotient : Compᵇ(𝒜) ⥤ HomotopyCategory.Bounded 𝒜 :=
  ObjectProperty.FullSubcategory.restrict
    (HomotopyCategory.quotient 𝒜 (up ℤ)) (quotientMapsTo 𝒜)

/-- Forgetting bounded structure after the homotopy quotient recovers the ambient homotopy
quotient. -/
@[stacks 013H "bounded homotopy quotient inclusion comparison"]
def quotientCompιIso :
    quotient 𝒜 ⋙ ι 𝒜 ≅
      CochainComplex.Bounded.ι 𝒜 ⋙ HomotopyCategory.quotient 𝒜 (up ℤ) :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (HomotopyCategory.quotient 𝒜 (up ℤ)) (quotientMapsTo 𝒜)

/-- The bounded homotopy quotient retains the object of the ambient homotopy quotient. -/
@[simp]
theorem quotient_obj_obj (K : CochainComplex.Bounded 𝒜) :
    ((quotient 𝒜).obj K).obj =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj := sorry

/-- The bounded homotopy quotient retains the morphism of the ambient homotopy quotient. -/
@[simp]
theorem quotient_map_hom {K L : CochainComplex.Bounded 𝒜} (f : K ⟶ L) :
    ((quotient 𝒜).map f).hom =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map f.hom := sorry

/-- The forward bounded quotient inclusion comparison is componentwise the identity. -/
@[simp]
theorem quotientCompιIso_hom_app (K : CochainComplex.Bounded 𝒜) :
    (quotientCompιIso 𝒜).hom.app K =
      𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj) := sorry

/-- The inverse bounded quotient inclusion comparison is componentwise the identity. -/
@[simp]
theorem quotientCompιIso_inv_app (K : CochainComplex.Bounded 𝒜) :
    (quotientCompιIso 𝒜).inv.app K =
      𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj) := sorry

end HomotopyCategory.Bounded

end CategoryTheory

namespace HomotopyCategory.Plus

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]

/-- The ambient homotopy quotient carries bounded-below complexes to bounded-below homotopy
objects. -/
@[stacks 013H "bounded-below homotopy quotient preservation"]
theorem quotientMapsTo :
    CochainComplex.plus 𝒜 ≤
      (HomotopyCategory.plus 𝒜).inverseImage
        (HomotopyCategory.quotient 𝒜 (up ℤ)) := sorry

/-- The bounded-below homotopy quotient retains the object of the ambient homotopy quotient. -/
@[simp]
theorem quotient_obj_obj (K : CochainComplex.Plus 𝒜) :
    ((quotient 𝒜).obj K).obj =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj := sorry

/-- The forward bounded-below quotient inclusion comparison is componentwise the identity. -/
@[simp]
theorem quotientCompιIso_hom_app (K : CochainComplex.Plus 𝒜) :
    (quotientCompιIso 𝒜).hom.app K =
      𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj) := sorry

/-- The inverse bounded-below quotient inclusion comparison is componentwise the identity. -/
@[simp]
theorem quotientCompιIso_inv_app (K : CochainComplex.Plus 𝒜) :
    (quotientCompιIso 𝒜).inv.app K =
      𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K.obj) := sorry

end HomotopyCategory.Plus


