/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.KernelPair.Operations
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction

/-!
# Postcomposition comparison of kernel pairs

Postcomposition of a morphism of groupoid fibrations induces a comparison
between its self two-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The comparison of kernel pairs induced by postcomposition with `f`,
sending `U ×_X U` to `U ×_Y U`. -/
def kernelPairMap {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    KernelPair.kernelPair.{u + 1, u, u + 1} p ⟶
      KernelPair.kernelPair.{u + 1, u, u + 1} (p ≫ f) :=
  TwoFibreProduct.map.{u + 1, u, u + 1, u}
    (CospanTransform.mk (𝟙 U) (𝟙 U) f (λ_ (p ≫ f)) (λ_ (p ≫ f)))

/-- `kernelPairMap p f` is the two-fibre-product map of the postcomposition
cospan with vertex maps `𝟙 U`, `𝟙 U`, and `f`. -/
theorem kernelPairMap_eq {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    kernelPairMap p f =
      TwoFibreProduct.map.{u + 1, u, u + 1, u}
        (CospanTransform.mk (𝟙 U) (𝟙 U) f (λ_ (p ≫ f)) (λ_ (p ≫ f))) := sorry

end AlgebraicGeometry.AlgebraicStack
