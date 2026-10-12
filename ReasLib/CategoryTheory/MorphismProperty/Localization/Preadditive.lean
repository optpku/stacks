/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Localizations

This file complements mathlib's left-fraction preadditive localization API with the dual
right-fraction construction.  The canonical localization also receives the additive and
finite-product instances needed to use it as an additive category.

The right-fraction instances have lower priority than mathlib's left-fraction instances.  Thus a
multiplicative system carrying both calculi uses the existing left-fraction owner, while a
right-only calculus still obtains the expected structure automatically.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

open MorphismProperty

namespace Localization

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u} [Category.{w} D]

/-- The preadditive structure transported from the opposite of a right-fraction localization. -/
@[implicit_reducible]
noncomputable def preadditiveOfHasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasRightCalculusOfFractions] : Preadditive D :=
  @Preadditive.ofFullyFaithful D _ Dᵒᵖᵒᵖ _
    (@instPreadditiveOpposite Dᵒᵖ _ (preadditive L.op W.op)) (opOp D)
      (Functor.FullyFaithful.ofFullyFaithful (opOp D))

/-- The right-fraction preadditive structure makes the localization functor additive. -/
theorem functorAdditiveOfHasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasRightCalculusOfFractions] :
    @L.Additive C D _ _ _ (preadditiveOfHasRightCalculusOfFractions L W) := sorry

/-- An additive preadditive structure on the target of a left-fraction localization is uniquely
the canonical one. -/
theorem preadditive_eq_of_additive_of_hasLeftCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] (P : Preadditive D)
    (hP : @L.Additive C D _ _ _ P) : P = preadditive L W := sorry

/-- An additive preadditive structure on the target of a right-fraction localization is uniquely
the structure transported from the opposite localization. -/
theorem preadditive_eq_of_additive_of_hasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasRightCalculusOfFractions] (P : Preadditive D)
    (hP : @L.Additive C D _ _ _ P) :
    P = preadditiveOfHasRightCalculusOfFractions L W := sorry

/-- A localization by a left or right calculus of fractions has a unique preadditive structure
making the localization functor additive. -/
@[stacks 05QD]
theorem existsUniquePreadditive
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (hW : W.HasLeftCalculusOfFractions ∨ W.HasRightCalculusOfFractions) :
    ∃! P : Preadditive D, @L.Additive C D _ _ _ P := sorry

end Localization

namespace MorphismProperty.Localization

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The canonical localization is preadditive when only a right calculus of fractions is
available.  Its low priority avoids a diamond with mathlib's left-fraction instance. -/
noncomputable instance (priority := 100) instPreadditiveOfHasRightCalculusOfFractions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] : Preadditive W.Localization :=
  Localization.preadditiveOfHasRightCalculusOfFractions W.Q W

/-- The canonical right-fraction localization functor is additive. -/
instance (priority := 100) instQAdditiveOfHasRightCalculusOfFractions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] : W.Q.Additive :=
  Localization.functorAdditiveOfHasRightCalculusOfFractions W.Q W

/-- A right-fraction localization of a category with a zero object has a zero object. -/
noncomputable instance (priority := 100) instHasZeroObjectOfHasRightCalculusOfFractions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] [HasZeroObject C] :
    HasZeroObject W.Localization := sorry

/-- A left-fraction localization of an additive category has finite products. -/
noncomputable instance (priority := 110) instHasFiniteProductsOfHasLeftCalculusOfFractions
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] [HasFiniteProducts C] :
    HasFiniteProducts W.Localization := sorry

/-- A right-fraction localization of an additive category has finite products. -/
noncomputable instance (priority := 100) instHasFiniteProductsOfHasRightCalculusOfFractions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] [HasFiniteProducts C] :
    HasFiniteProducts W.Localization := sorry

/-- Localization by either calculus of fractions preserves the existence of finite products of an
additive source category. -/
@[stacks 05QE]
theorem hasFiniteProducts
    (W : MorphismProperty C) [HasFiniteProducts C]
    (hW : W.HasLeftCalculusOfFractions ∨ W.HasRightCalculusOfFractions) :
    HasFiniteProducts W.Localization := sorry

variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
  [W.HasRightCalculusOfFractions]

/-- A localized object is zero exactly when a zero morphism out of it is inverted. -/
theorem objectIsZero_iff_exists_zero_out (X : C) :
    IsZero (W.Q.obj X) ↔ ∃ Y : C, W (0 : X ⟶ Y) := sorry

/-- A localized object is zero exactly when a zero morphism into it is inverted. -/
theorem objectIsZero_iff_exists_zero_in (X : C) :
    IsZero (W.Q.obj X) ↔ ∃ Y : C, W (0 : Y ⟶ X) := sorry

/-- The zero-object criterion for an object in an additive localization, in its symmetric
three-condition form. -/
@[stacks 05QF]
theorem objectIsZero_tfae (X : C) :
    List.TFAE [IsZero (W.Q.obj X), ∃ Y : C, W (0 : X ⟶ Y), ∃ Y : C, W (0 : Y ⟶ X)] :=
  sorry

end MorphismProperty.Localization

end CategoryTheory
