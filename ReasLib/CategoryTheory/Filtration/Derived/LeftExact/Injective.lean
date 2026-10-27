/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact
public import ReasLib.CategoryTheory.Filtration.Derived.Injective

/-! Computation of filtered right-derived functors on filtered-injective complexes. -/

@[expose] public section

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]

/-- Applying a left-exact functor to bounded-below finite filtered-injective homotopy
complexes gives bounded-below finite filtered homotopy complexes. -/
noncomputable def injectiveHomotopy (T : A ⥤ₗ B) :
    HomotopyCategory.Plus (Finite.FilteredInjective.category A) ⥤
      HomotopyCategory.Plus (Finite.category B) :=
  (Finite.FilteredInjective.inclusion A).mapHomotopyCategoryPlus ⋙ homotopy T

variable [HasDerivedCategory (GradedObject ℤ A)]
  [HasDerivedCategory (GradedObject ℤ B)]
variable (T : A ⥤ₗ B)
variable (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B)

/-- The canonical filtered right-derived unit restricted to bounded-below
filtered-injective homotopy complexes. -/
noncomputable def injectiveUnit [Has T hB] :
    (Finite.FilteredInjective.inclusion A).mapHomotopyCategoryPlus ⋙
        (homotopy T ⋙ Plus.Quotient.functor B hB) ⟶
      (Finite.FilteredInjective.inclusion A).mapHomotopyCategoryPlus ⋙
        (Plus.Quotient.functor A hA ⋙ functor T hA hB) :=
  Functor.whiskerLeft (Finite.FilteredInjective.inclusion A).mapHomotopyCategoryPlus
    (unit T hA hB)

/-- The restricted unit at a filtered-injective complex is the canonical unit at its
underlying filtered homotopy complex. -/
@[simp]
theorem injectiveUnit_app [Has T hB]
    (K : HomotopyCategory.Plus (Finite.FilteredInjective.category A)) :
    (injectiveUnit T hA hB).app K =
      (unit T hA hB).app
        (((Finite.FilteredInjective.inclusion A).mapHomotopyCategoryPlus).obj K) := rfl

/-- When the source has enough injectives, the filtered right-derived unit is invertible
on bounded-below filtered-injective homotopy complexes. -/
instance isIso_injectiveUnit [Has T hB] [EnoughInjectives A] :
    IsIso (injectiveUnit T hA hB) := sorry

/-- The filtered right-derived functor is computed by applying the original functor to
filtered-injective homotopy complexes and then localizing. -/
noncomputable def diagramIso [Has T hB] [EnoughInjectives A] :
    Plus.FilteredInjective.functor A hA ⋙ functor T hA hB ≅
      injectiveHomotopy T ⋙ Plus.Quotient.functor B hB :=
  Functor.associator
      (Finite.FilteredInjective.inclusion A).mapHomotopyCategoryPlus
      (Plus.Quotient.functor A hA) (functor T hA hB) ≪≫
    (asIso (injectiveUnit T hA hB)).symm ≪≫
    (Functor.associator
      (Finite.FilteredInjective.inclusion A).mapHomotopyCategoryPlus
      (homotopy T) (Plus.Quotient.functor B hB)).symm

/-- The inverse of the filtered-injective comparison is the canonical derived unit
evaluated on the underlying filtered homotopy complex. -/
theorem diagramIso_inv_app [Has T hB] [EnoughInjectives A]
    (K : HomotopyCategory.Plus (Finite.FilteredInjective.category A)) :
    (diagramIso T hA hB).inv.app K =
      (unit T hA hB).app
        (((Finite.FilteredInjective.inclusion A).mapHomotopyCategoryPlus).obj K) := sorry

end CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact

