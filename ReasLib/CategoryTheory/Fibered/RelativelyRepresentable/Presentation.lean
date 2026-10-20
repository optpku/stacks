/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.FullyFaithful

/-!
# Slice presentations of relatively representable morphisms
-/

@[expose] public section

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable

open scoped Bicategory TwoFibreProduct

variable {C : Type u} [Category.{v} C]

/-- For a chosen slice presentation of a two-fibre product, the transported first projection
is isomorphic to the canonical slice map induced by its terminal-object evaluation. -/
theorem overMap_eval_fst
    {X Y : FiberedCategoryOver.Groupoids C} {f : X ⟶ Y} {U V : C}
    (y : slice U ⟶ Y) (e : slice V ≌ TwoFibreProduct.apex y f) :
    Nonempty
      (overMap (slice.eval (e.hom ≫ TwoFibreProduct.fst y f)) ≅
        e.hom ≫ TwoFibreProduct.fst y f) := sorry

/-- A relatively representable morphism admits a slice presentation of each two-fibre product
along a morphism from a canonical slice fibration. -/
theorem exists_slicePresentation
    {X Y : FiberedCategoryOver.Groupoids C} {f : X ⟶ Y}
    (hf : relativelyRepresentable f) {U : C} (y : slice U ⟶ Y) :
    ∃ V : C, Nonempty (slice V ≌ TwoFibreProduct.apex y f) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable
