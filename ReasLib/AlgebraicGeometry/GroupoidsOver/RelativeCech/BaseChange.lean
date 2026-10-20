/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Comparison
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

/-!
# Base change of relative Čech complexes

The canonical relative Čech comparison is an isomorphism along a 2-cartesian
square of categories fibred in groupoids over schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids Bicategory
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- For a 2-cartesian square of categories fibred in groupoids over a scheme,
the canonical inverse-image comparison of relative Čech complexes with abelian
presheaf coefficients is an isomorphism. -/
theorem relativeCechMap_isIso_of_twoFibreProduct {V Y : GroupoidsOver S}
    (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U) (e : Y ⟶ X) (t : h ≫ f ≅ g ≫ e)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h_twoFibre : PseudoPullbackCone.IsBilimit
      (⟨V, g, h, t.symm⟩ : PseudoPullbackCone e f)) :
    IsIso (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.map t F) :=
  sorry

/-- On the chosen 2-fibre product of morphisms of categories fibred in groupoids
over a scheme, the canonical relative Čech comparison is an isomorphism. -/
instance relativeCechMap_isIso_twoFibreProduct {Y : GroupoidsOver S}
    (f : U ⟶ X) (e : Y ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.map
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} e f).symm F) :=
  relativeCechMap_isIso_of_twoFibreProduct f
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} e f)
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} e f) e
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} e f).symm F
    (TwoFibreProduct.cone.isBilimit e f)

end AlgebraicGeometry.GroupoidsOver
