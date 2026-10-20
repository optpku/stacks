/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Forget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of the finite filtered forgetful derived comparison

The localization factorization is already owned by `Derived.Forget`.  This leaf exposes its
homotopy-level naturality equations in a form that downstream computations can rewrite directly.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived.Forget.Computation

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- Naturality of the forward finite filtered forgetful factorization comparison. -/
@[reassoc (attr := simp), stacks 05S3 "finite filtered forgetful derived computation"]
theorem facIso_hom_naturality
    (h_inverts : Forget.Inverts C)
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (Forget.lift C h_inverts).map ((Quotient.functor C).map f) ≫
        (Forget.facIso C h_inverts).hom.app L =
      (Forget.facIso C h_inverts).hom.app K ≫ (Forget.homotopy C).map f := sorry

/-- Naturality of the inverse finite filtered forgetful factorization comparison. -/
@[reassoc (attr := simp), stacks 05S3 "finite filtered forgetful derived computation"]
theorem facIso_inv_naturality
    (h_inverts : Forget.Inverts C)
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (Forget.homotopy C).map f ≫ (Forget.facIso C h_inverts).inv.app L =
      (Forget.facIso C h_inverts).inv.app K ≫
        (Forget.lift C h_inverts).map ((Quotient.functor C).map f) := sorry

/-- Naturality of the canonical forward finite filtered forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S3 "canonical finite filtered forgetful derived computation"]
theorem canonicalFacIso_hom_naturality
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (Forget.canonicalLift C).map ((Quotient.functor C).map f) ≫
        (Forget.canonicalFacIso C).hom.app L =
      (Forget.canonicalFacIso C).hom.app K ≫ (Forget.homotopy C).map f := sorry

/-- Naturality of the canonical inverse finite filtered forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S3 "canonical finite filtered forgetful derived computation"]
theorem canonicalFacIso_inv_naturality
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (Forget.homotopy C).map f ≫ (Forget.canonicalFacIso C).inv.app L =
      (Forget.canonicalFacIso C).inv.app K ≫
        (Forget.canonicalLift C).map ((Quotient.functor C).map f) := sorry

end CategoryTheory.FilteredObject.FiniteDerived.Forget.Computation
