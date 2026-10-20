/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.CountableProducts
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Products
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Countable Products in Derived Categories

Exact countable products in an abelian category induce countable products in any chosen derived
localization.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u uI

namespace CategoryTheory.DerivedCategory.Product

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- An abelian category with exact countable products has countable products in its derived
category. -/
@[stacks 07KC]
instance hasCountableProducts_of_countableAB4Star
    [HasCountableProducts A] [CountableAB4Star A] :
    HasCountableProducts (DerivedCategory A) := sorry

/-- For a countable family of complexes, its termwise product and canonical projections form a
product fan after passage to any chosen derived localization under `CountableAB4Star`. -/
@[stacks 07KC "countable termwise product model"]
noncomputable def fanIsLimit_of_countableAB4Star
    [HasCountableProducts A] [CountableAB4Star A]
    {J : Type uI} [Countable J] (K : J → CochainComplex A ℤ) :
    IsLimit
      (Fan.mk
        (DerivedCategory.Q.obj (∏ᶜ K))
        (fun j ↦ DerivedCategory.Q.map (Pi.π K j))) :=
  fanIsLimit_of_termwise K

end CategoryTheory.DerivedCategory.Product
