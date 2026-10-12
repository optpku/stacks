/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.ProductSlice
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Construction
public import ReasLib.CategoryTheory.Fibered.InSets.Slice
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Product-slice bridge for two-fibre products in groupoids

The general product-slice construction is owned by
`BasedCategory.PseudoPullback.ProductSlice`. This leaf contains only the
bridge from a two-fibre product of categories fibred in groupoids to that
general construction.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids (slice)

variable {C : Type u} [Category.{v} C]
variable [Limits.HasBinaryProducts C]

namespace TwoFibreProduct

/-- The product-slice map for the fibred-in-groupoids two-fibre product. -/
@[stacks 04SF "product-slice map for a two-fibre product"]
noncomputable def toProductSlice
    {X : FiberedCategoryOver.Groupoids C} {U V : C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    FiberedCategoryOver.Groupoids.total
      (TwoFibreProduct.apex G' G) ⥤ Over (Limits.prod U V) :=
  (BasedCategory.PseudoPullback.swap
      (FiberedCategoryOver.Groupoids.toBasedFunctor G')
      (FiberedCategoryOver.Groupoids.toBasedFunctor G)).toFunctor ⋙
    BasedCategory.PseudoPullback.ProductSlice.toProduct
      (F := FiberedCategoryOver.Groupoids.toBasedFunctor G)
      (G := FiberedCategoryOver.Groupoids.toBasedFunctor G')

namespace toProductSlice

/-- The fibred-in-groupoids product-slice map is strictly over `C`. -/
@[simp]
theorem comp_forget
    {X : FiberedCategoryOver.Groupoids C} {U V : C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    TwoFibreProduct.toProductSlice G G' ⋙
        Over.forget (Limits.prod U V) =
      FiberedCategoryOver.Groupoids.p
        (TwoFibreProduct.apex G' G) := sorry
/- Proof strategy: unfold `TwoFibreProduct.toProductSlice` and use
`BasedCategory.PseudoPullback.ProductSlice.toProduct.comp_forget`. -/

namespace obj

/-- The product-slice image of an explicit two-fibre-product object has its common
pseudo-pullback base object as its slice domain. -/
@[simp]
theorem left
    {X : FiberedCategoryOver.Groupoids C} {U V : C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (P : FiberedCategoryOver.Groupoids.total (TwoFibreProduct.apex G' G)) :
    (TwoFibreProduct.toProductSlice G G' |>.obj P).left =
      BasedCategory.PseudoPullback.baseObj P := sorry

namespace hom

/-- The first product projection of the product-slice image is the transported second slice
component of the original two-fibre-product object. -/
@[simp]
theorem fst
    {X : FiberedCategoryOver.Groupoids C} {U V : C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (P : FiberedCategoryOver.Groupoids.total (TwoFibreProduct.apex G' G)) :
    (TwoFibreProduct.toProductSlice G G' |>.obj P).hom ≫
        Limits.prod.fst =
      (BasedCategory.PseudoPullback.sndBaseIso P).inv ≫
        (BasedCategory.PseudoPullback.fiberObj P).snd.1.hom := sorry

/-- The second product projection of the product-slice image is the transported first slice
component of the original two-fibre-product object. -/
@[simp]
theorem snd
    {X : FiberedCategoryOver.Groupoids C} {U V : C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (P : FiberedCategoryOver.Groupoids.total (TwoFibreProduct.apex G' G)) :
    (TwoFibreProduct.toProductSlice G G' |>.obj P).hom ≫
        Limits.prod.snd =
      (BasedCategory.PseudoPullback.fstBaseIso P).inv ≫
        (BasedCategory.PseudoPullback.fiberObj P).fst.1.hom := sorry

end hom

end obj

namespace map

/-- On morphisms, the product-slice bridge retains the original common base map as its
underlying slice map. -/
@[simp]
theorem left
    {X : FiberedCategoryOver.Groupoids C} {U V : C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    {P Q : FiberedCategoryOver.Groupoids.total (TwoFibreProduct.apex G' G)}
    (φ : P ⟶ Q) :
    (TwoFibreProduct.toProductSlice G G' |>.map φ).left =
      BasedCategory.PseudoPullback.baseMap φ := sorry

end map

end toProductSlice

end TwoFibreProduct

end CategoryTheory
