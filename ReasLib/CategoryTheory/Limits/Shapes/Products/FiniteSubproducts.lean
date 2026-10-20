/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered

/-!
# Products as limits of finite subproducts

This file gives the finite-subproducts limiting cone using only finite products
and the chosen product of the indexed family.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.Limits.ProductsFromFiniteCofiltered

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {α : Type v}

/-- The morphism from a cone over the finite subproducts to the product, obtained
by using its legs at singleton finite subsets. -/
noncomputable def finiteSubproductsConeLift (f : α → C) [HasProduct f]
    (s : Cone (liftToFinsetObj (Discrete.functor f))) :
    s.pt ⟶ (finiteSubproductsCone f).pt :=
  Pi.lift fun j =>
    s.π.app (Opposite.op ({Discrete.mk j} : Finset (Discrete α))) ≫
      (Pi.π (fun x : ({Discrete.mk j} : Finset (Discrete α)) => f x.1.as)
        (⟨Discrete.mk j, by simp⟩ : ({Discrete.mk j} : Finset (Discrete α))) :
          (∏ᶜ fun x : ({Discrete.mk j} : Finset (Discrete α)) => f x.1.as) ⟶ f j)

/-- The morphism induced from a cone over the finite subproducts commutes with
every finite-stage projection. -/
theorem finiteSubproductsConeLift_fac (f : α → C) [HasProduct f]
    (s : Cone (liftToFinsetObj (Discrete.functor f)))
    (j : (Finset (Discrete α))ᵒᵖ) :
    finiteSubproductsConeLift f s ≫ (finiteSubproductsCone f).π.app j = s.π.app j := sorry

/-- A morphism to the product is determined by its composites with all
finite-stage projections. -/
theorem finiteSubproductsConeLift_uniq (f : α → C) [HasProduct f]
    (s : Cone (liftToFinsetObj (Discrete.functor f)))
    (m : s.pt ⟶ (finiteSubproductsCone f).pt)
    (h : ∀ j, m ≫ (finiteSubproductsCone f).π.app j = s.π.app j) :
    m = finiteSubproductsConeLift f s := sorry

/-- If an indexed product exists, its cone to the finite subproducts is a
limiting cone, assuming only the existence of finite products. -/
noncomputable def isLimitFiniteSubproductsConeOfHasProduct
    (f : α → C) [HasProduct f] : IsLimit (finiteSubproductsCone f) where
  lift := finiteSubproductsConeLift f
  fac := finiteSubproductsConeLift_fac f
  uniq := finiteSubproductsConeLift_uniq f

end CategoryTheory.Limits.ProductsFromFiniteCofiltered
