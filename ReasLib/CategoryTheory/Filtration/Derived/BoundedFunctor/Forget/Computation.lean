/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Minus
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Bounded
public import ReasLib.CategoryTheory.Localization.Lifting.Computation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of bounded forgetful comparisons

The forgetful bounded derived functors are localization descents.  The model-independent
equations live in `Localization.Lifting.iso`; this leaf exposes concrete rewrite specializations
in both directions without unfolding the localization construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]
variable (h_derived :
  _root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.Inverts C)

namespace Plus.Forget.Computation

/-- Naturality of the forward bounded-below forgetful factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-below forgetful computation"]
theorem facIso_hom_naturality
    (h : Plus.Forget.Inverts C)
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.Forget.lift C h_derived h).map
        ((Plus.Quotient.functor C h_derived).map f) ≫
      (Plus.Forget.facIso C h_derived h).hom.app L =
    (Plus.Forget.facIso C h_derived h).hom.app K ≫
      (Plus.Forget.homotopy C).map f := sorry

/-- Naturality of the inverse bounded-below forgetful factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-below forgetful computation"]
theorem facIso_inv_naturality
    (h : Plus.Forget.Inverts C)
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.Forget.homotopy C).map f ≫
        (Plus.Forget.facIso C h_derived h).inv.app L =
      (Plus.Forget.facIso C h_derived h).inv.app K ≫
        (Plus.Forget.lift C h_derived h).map
          ((Plus.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded-below forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-below forgetful computation"]
theorem canonicalFacIso_hom_naturality
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.Forget.canonicalLift C).map
        ((Plus.Quotient.canonicalFunctor C).map f) ≫
      (Plus.Forget.canonicalFacIso C).hom.app L =
    (Plus.Forget.canonicalFacIso C).hom.app K ≫
      (Plus.Forget.homotopy C).map f := sorry

/-- Naturality of the inverse canonical bounded-below forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-below forgetful computation"]
theorem canonicalFacIso_inv_naturality
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.Forget.homotopy C).map f ≫
        (Plus.Forget.canonicalFacIso C).inv.app L =
      (Plus.Forget.canonicalFacIso C).inv.app K ≫
        (Plus.Forget.canonicalLift C).map
          ((Plus.Quotient.canonicalFunctor C).map f) := sorry

end Plus.Forget.Computation

namespace Minus.Forget.Computation

/-- Naturality of the forward bounded-above forgetful factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-above forgetful computation"]
theorem facIso_hom_naturality
    (h : Minus.Forget.Inverts C)
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.Forget.lift C h_derived h).map
        ((Minus.Quotient.functor C h_derived).map f) ≫
      (Minus.Forget.facIso C h_derived h).hom.app L =
    (Minus.Forget.facIso C h_derived h).hom.app K ≫
      (Minus.Forget.homotopy C).map f := sorry

/-- Naturality of the inverse bounded-above forgetful factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-above forgetful computation"]
theorem facIso_inv_naturality
    (h : Minus.Forget.Inverts C)
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.Forget.homotopy C).map f ≫
        (Minus.Forget.facIso C h_derived h).inv.app L =
      (Minus.Forget.facIso C h_derived h).inv.app K ≫
        (Minus.Forget.lift C h_derived h).map
          ((Minus.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded-above forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-above forgetful computation"]
theorem canonicalFacIso_hom_naturality
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.Forget.canonicalLift C).map
        ((Minus.Quotient.canonicalFunctor C).map f) ≫
      (Minus.Forget.canonicalFacIso C).hom.app L =
    (Minus.Forget.canonicalFacIso C).hom.app K ≫
      (Minus.Forget.homotopy C).map f := sorry

/-- Naturality of the inverse canonical bounded-above forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-above forgetful computation"]
theorem canonicalFacIso_inv_naturality
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.Forget.homotopy C).map f ≫
        (Minus.Forget.canonicalFacIso C).inv.app L =
      (Minus.Forget.canonicalFacIso C).inv.app K ≫
        (Minus.Forget.canonicalLift C).map
          ((Minus.Quotient.canonicalFunctor C).map f) := sorry

end Minus.Forget.Computation

namespace Bounded.Forget.Computation

/-- Naturality of the forward bounded forgetful factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded forgetful computation"]
theorem facIso_hom_naturality
    (h : Bounded.Forget.Inverts C)
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.Forget.lift C h_derived h).map
        ((Bounded.Quotient.functor C h_derived).map f) ≫
      (Bounded.Forget.facIso C h_derived h).hom.app L =
    (Bounded.Forget.facIso C h_derived h).hom.app K ≫
      (Bounded.Forget.homotopy C).map f := sorry

/-- Naturality of the inverse bounded forgetful factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded forgetful computation"]
theorem facIso_inv_naturality
    (h : Bounded.Forget.Inverts C)
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.Forget.homotopy C).map f ≫
        (Bounded.Forget.facIso C h_derived h).inv.app L =
      (Bounded.Forget.facIso C h_derived h).inv.app K ≫
        (Bounded.Forget.lift C h_derived h).map
          ((Bounded.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded forgetful computation"]
theorem canonicalFacIso_hom_naturality
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.Forget.canonicalLift C).map
        ((Bounded.Quotient.canonicalFunctor C).map f) ≫
      (Bounded.Forget.canonicalFacIso C).hom.app L =
    (Bounded.Forget.canonicalFacIso C).hom.app K ≫
      (Bounded.Forget.homotopy C).map f := sorry

/-- Naturality of the inverse canonical bounded forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded forgetful computation"]
theorem canonicalFacIso_inv_naturality
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.Forget.homotopy C).map f ≫
        (Bounded.Forget.canonicalFacIso C).inv.app L =
      (Bounded.Forget.canonicalFacIso C).inv.app K ≫
        (Bounded.Forget.canonicalLift C).map
          ((Bounded.Quotient.canonicalFunctor C).map f) := sorry

end Bounded.Forget.Computation

end CategoryTheory.FilteredObject.FiniteDerived
