/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine
public import ReasLib.CategoryTheory.Limits.Shapes.Products.FiniteSubproducts

/-!
# Products of affine schemes over a base

This file constructs products of affine morphisms over a fixed base scheme and
records the affineness of their projections to finite subproducts.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.Limits.ProductsFromFiniteCofiltered

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over

variable {I : Type u} (S : Scheme.{u})
variable (T : I → CategoryTheory.Over S)

/-- Every transition morphism between finite subproducts of affine morphisms
over a fixed base scheme is affine. -/
instance instIsAffineHomFiniteSubproductsMap
    [∀ i, IsAffineHom (T i).hom]
    {s t : (Finset (Discrete I))ᵒᵖ} (f : s ⟶ t) :
    IsAffineHom ((liftToFinsetObj (Discrete.functor T)).map f).left := sorry

/-- An arbitrary indexed family of affine morphisms into a fixed base scheme
admits a product in the slice category over that scheme. -/
instance instHasProductOfIsAffineHom
    [h_affine : ∀ i, IsAffineHom (T i).hom] : HasProduct T := sorry

/-- The projection from the product of affine morphisms to every finite
subproduct is an affine morphism of schemes. -/
theorem isAffineHom_finiteSubproductsCone_π_app
    [∀ i, IsAffineHom (T i).hom]
    (s : (Finset (Discrete I))ᵒᵖ) :
    IsAffineHom ((finiteSubproductsCone T).π.app s).left := sorry

end AlgebraicGeometry.Scheme.Over
