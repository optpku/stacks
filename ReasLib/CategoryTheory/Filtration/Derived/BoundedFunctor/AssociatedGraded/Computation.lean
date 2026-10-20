/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.AssociatedGraded
public import ReasLib.CategoryTheory.Localization.Lifting.Computation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of bounded associated-graded comparisons

The bounded associated-graded functors are descended from the corresponding homotopy functors.
The model-independent equations live in `Localization.Lifting.iso`; this leaf retains
rewrite-ready specializations under the concrete bounded functor namespaces.
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

namespace Plus.AssociatedGraded.Computation

/-- Naturality of the forward bounded-below associated-graded factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-below associated-graded computation"]
theorem facIso_hom_naturality
    (h : Plus.AssociatedGraded.Inverts C)
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.AssociatedGraded.lift C h_derived h).map
        ((Plus.Quotient.functor C h_derived).map f) ≫
      (Plus.AssociatedGraded.facIso C h_derived h).hom.app L =
    (Plus.AssociatedGraded.facIso C h_derived h).hom.app K ≫
      (Plus.AssociatedGraded.homotopy C).map f := sorry

/-- Naturality of the inverse bounded-below associated-graded factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-below associated-graded computation"]
theorem facIso_inv_naturality
    (h : Plus.AssociatedGraded.Inverts C)
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.AssociatedGraded.homotopy C).map f ≫
        (Plus.AssociatedGraded.facIso C h_derived h).inv.app L =
      (Plus.AssociatedGraded.facIso C h_derived h).inv.app K ≫
        (Plus.AssociatedGraded.lift C h_derived h).map
          ((Plus.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded-below associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-below associated-graded computation"]
theorem canonicalFacIso_hom_naturality
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.AssociatedGraded.canonicalLift C).map
        ((Plus.Quotient.canonicalFunctor C).map f) ≫
      (Plus.AssociatedGraded.canonicalFacIso C).hom.app L =
    (Plus.AssociatedGraded.canonicalFacIso C).hom.app K ≫
      (Plus.AssociatedGraded.homotopy C).map f := sorry

/-- Naturality of the inverse canonical bounded-below associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-below associated-graded computation"]
theorem canonicalFacIso_inv_naturality
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.AssociatedGraded.homotopy C).map f ≫
        (Plus.AssociatedGraded.canonicalFacIso C).inv.app L =
      (Plus.AssociatedGraded.canonicalFacIso C).inv.app K ≫
        (Plus.AssociatedGraded.canonicalLift C).map
          ((Plus.Quotient.canonicalFunctor C).map f) := sorry

end Plus.AssociatedGraded.Computation

namespace Minus.AssociatedGraded.Computation

/-- Naturality of the forward bounded-above associated-graded factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-above associated-graded computation"]
theorem facIso_hom_naturality
    (h : Minus.AssociatedGraded.Inverts C)
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.AssociatedGraded.lift C h_derived h).map
        ((Minus.Quotient.functor C h_derived).map f) ≫
      (Minus.AssociatedGraded.facIso C h_derived h).hom.app L =
    (Minus.AssociatedGraded.facIso C h_derived h).hom.app K ≫
      (Minus.AssociatedGraded.homotopy C).map f := sorry

/-- Naturality of the inverse bounded-above associated-graded factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-above associated-graded computation"]
theorem facIso_inv_naturality
    (h : Minus.AssociatedGraded.Inverts C)
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.AssociatedGraded.homotopy C).map f ≫
        (Minus.AssociatedGraded.facIso C h_derived h).inv.app L =
      (Minus.AssociatedGraded.facIso C h_derived h).inv.app K ≫
        (Minus.AssociatedGraded.lift C h_derived h).map
          ((Minus.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded-above associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-above associated-graded computation"]
theorem canonicalFacIso_hom_naturality
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.AssociatedGraded.canonicalLift C).map
        ((Minus.Quotient.canonicalFunctor C).map f) ≫
      (Minus.AssociatedGraded.canonicalFacIso C).hom.app L =
    (Minus.AssociatedGraded.canonicalFacIso C).hom.app K ≫
      (Minus.AssociatedGraded.homotopy C).map f := sorry

/-- Naturality of the inverse canonical bounded-above associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-above associated-graded computation"]
theorem canonicalFacIso_inv_naturality
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.AssociatedGraded.homotopy C).map f ≫
        (Minus.AssociatedGraded.canonicalFacIso C).inv.app L =
      (Minus.AssociatedGraded.canonicalFacIso C).inv.app K ≫
        (Minus.AssociatedGraded.canonicalLift C).map
          ((Minus.Quotient.canonicalFunctor C).map f) := sorry

end Minus.AssociatedGraded.Computation

namespace Bounded.AssociatedGraded.Computation

/-- Naturality of the forward bounded associated-graded factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded associated-graded computation"]
theorem facIso_hom_naturality
    (h : Bounded.AssociatedGraded.Inverts C)
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.AssociatedGraded.lift C h_derived h).map
        ((Bounded.Quotient.functor C h_derived).map f) ≫
      (Bounded.AssociatedGraded.facIso C h_derived h).hom.app L =
    (Bounded.AssociatedGraded.facIso C h_derived h).hom.app K ≫
      (Bounded.AssociatedGraded.homotopy C).map f := sorry

/-- Naturality of the inverse bounded associated-graded factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded associated-graded computation"]
theorem facIso_inv_naturality
    (h : Bounded.AssociatedGraded.Inverts C)
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.AssociatedGraded.homotopy C).map f ≫
        (Bounded.AssociatedGraded.facIso C h_derived h).inv.app L =
      (Bounded.AssociatedGraded.facIso C h_derived h).inv.app K ≫
        (Bounded.AssociatedGraded.lift C h_derived h).map
          ((Bounded.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded associated-graded computation"]
theorem canonicalFacIso_hom_naturality
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.AssociatedGraded.canonicalLift C).map
        ((Bounded.Quotient.canonicalFunctor C).map f) ≫
      (Bounded.AssociatedGraded.canonicalFacIso C).hom.app L =
    (Bounded.AssociatedGraded.canonicalFacIso C).hom.app K ≫
      (Bounded.AssociatedGraded.homotopy C).map f := sorry

/-- Naturality of the inverse canonical bounded associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded associated-graded computation"]
theorem canonicalFacIso_inv_naturality
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.AssociatedGraded.homotopy C).map f ≫
        (Bounded.AssociatedGraded.canonicalFacIso C).inv.app L =
      (Bounded.AssociatedGraded.canonicalFacIso C).inv.app K ≫
        (Bounded.AssociatedGraded.canonicalLift C).map
          ((Bounded.Quotient.canonicalFunctor C).map f) := sorry

end Bounded.AssociatedGraded.Computation

end CategoryTheory.FilteredObject.FiniteDerived
