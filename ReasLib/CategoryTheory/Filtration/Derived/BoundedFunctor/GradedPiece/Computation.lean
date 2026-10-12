/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Minus
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Bounded
public import ReasLib.CategoryTheory.Localization.Lifting.Computation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of bounded graded-piece comparisons

The bounded graded-piece functors are localization descents of their homotopy-level versions.
The model-independent equations live in `Localization.Lifting.iso`; the equations below are
concrete rewrite specializations that avoid unfolding the universal localization lift.
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

namespace Plus.GradedPiece.Computation

/-- Naturality of the forward bounded-below graded-piece factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-below graded-piece computation"]
theorem facIso_hom_naturality
    (p : ℤ) (h : Plus.GradedPiece.Inverts C p)
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.GradedPiece.lift C h_derived p h).map
        ((Plus.Quotient.functor C h_derived).map f) ≫
      (Plus.GradedPiece.facIso C h_derived p h).hom.app L =
    (Plus.GradedPiece.facIso C h_derived p h).hom.app K ≫
      (Plus.GradedPiece.homotopy C p).map f := sorry

/-- Naturality of the inverse bounded-below graded-piece factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-below graded-piece computation"]
theorem facIso_inv_naturality
    (p : ℤ) (h : Plus.GradedPiece.Inverts C p)
    {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.GradedPiece.homotopy C p).map f ≫
        (Plus.GradedPiece.facIso C h_derived p h).inv.app L =
      (Plus.GradedPiece.facIso C h_derived p h).inv.app K ≫
        (Plus.GradedPiece.lift C h_derived p h).map
          ((Plus.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded-below graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-below graded-piece computation"]
theorem canonicalFacIso_hom_naturality
    (p : ℤ) {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.GradedPiece.canonicalLift C p).map
        ((Plus.Quotient.canonicalFunctor C).map f) ≫
      (Plus.GradedPiece.canonicalFacIso C p).hom.app L =
    (Plus.GradedPiece.canonicalFacIso C p).hom.app K ≫
      (Plus.GradedPiece.homotopy C p).map f := sorry

/-- Naturality of the inverse canonical bounded-below graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-below graded-piece computation"]
theorem canonicalFacIso_inv_naturality
    (p : ℤ) {K L : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Plus.GradedPiece.homotopy C p).map f ≫
        (Plus.GradedPiece.canonicalFacIso C p).inv.app L =
      (Plus.GradedPiece.canonicalFacIso C p).inv.app K ≫
        (Plus.GradedPiece.canonicalLift C p).map
          ((Plus.Quotient.canonicalFunctor C).map f) := sorry

end Plus.GradedPiece.Computation

namespace Minus.GradedPiece.Computation

/-- Naturality of the forward bounded-above graded-piece factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-above graded-piece computation"]
theorem facIso_hom_naturality
    (p : ℤ) (h : Minus.GradedPiece.Inverts C p)
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.GradedPiece.lift C h_derived p h).map
        ((Minus.Quotient.functor C h_derived).map f) ≫
      (Minus.GradedPiece.facIso C h_derived p h).hom.app L =
    (Minus.GradedPiece.facIso C h_derived p h).hom.app K ≫
      (Minus.GradedPiece.homotopy C p).map f := sorry

/-- Naturality of the inverse bounded-above graded-piece factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded-above graded-piece computation"]
theorem facIso_inv_naturality
    (p : ℤ) (h : Minus.GradedPiece.Inverts C p)
    {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.GradedPiece.homotopy C p).map f ≫
        (Minus.GradedPiece.facIso C h_derived p h).inv.app L =
      (Minus.GradedPiece.facIso C h_derived p h).inv.app K ≫
        (Minus.GradedPiece.lift C h_derived p h).map
          ((Minus.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded-above graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-above graded-piece computation"]
theorem canonicalFacIso_hom_naturality
    (p : ℤ) {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.GradedPiece.canonicalLift C p).map
        ((Minus.Quotient.canonicalFunctor C).map f) ≫
      (Minus.GradedPiece.canonicalFacIso C p).hom.app L =
    (Minus.GradedPiece.canonicalFacIso C p).hom.app K ≫
      (Minus.GradedPiece.homotopy C p).map f := sorry

/-- Naturality of the inverse canonical bounded-above graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded-above graded-piece computation"]
theorem canonicalFacIso_inv_naturality
    (p : ℤ) {K L : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Minus.GradedPiece.homotopy C p).map f ≫
        (Minus.GradedPiece.canonicalFacIso C p).inv.app L =
      (Minus.GradedPiece.canonicalFacIso C p).inv.app K ≫
        (Minus.GradedPiece.canonicalLift C p).map
          ((Minus.Quotient.canonicalFunctor C).map f) := sorry

end Minus.GradedPiece.Computation

namespace Bounded.GradedPiece.Computation

/-- Naturality of the forward bounded graded-piece factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded graded-piece computation"]
theorem facIso_hom_naturality
    (p : ℤ) (h : Bounded.GradedPiece.Inverts C p)
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.GradedPiece.lift C h_derived p h).map
        ((Bounded.Quotient.functor C h_derived).map f) ≫
      (Bounded.GradedPiece.facIso C h_derived p h).hom.app L =
    (Bounded.GradedPiece.facIso C h_derived p h).hom.app K ≫
      (Bounded.GradedPiece.homotopy C p).map f := sorry

/-- Naturality of the inverse bounded graded-piece factorization comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded graded-piece computation"]
theorem facIso_inv_naturality
    (p : ℤ) (h : Bounded.GradedPiece.Inverts C p)
    {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.GradedPiece.homotopy C p).map f ≫
        (Bounded.GradedPiece.facIso C h_derived p h).inv.app L =
      (Bounded.GradedPiece.facIso C h_derived p h).inv.app K ≫
        (Bounded.GradedPiece.lift C h_derived p h).map
          ((Bounded.Quotient.functor C h_derived).map f) := sorry

/-- Naturality of the forward canonical bounded graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded graded-piece computation"]
theorem canonicalFacIso_hom_naturality
    (p : ℤ) {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.GradedPiece.canonicalLift C p).map
        ((Bounded.Quotient.canonicalFunctor C).map f) ≫
      (Bounded.GradedPiece.canonicalFacIso C p).hom.app L =
    (Bounded.GradedPiece.canonicalFacIso C p).hom.app K ≫
      (Bounded.GradedPiece.homotopy C p).map f := sorry

/-- Naturality of the inverse canonical bounded graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "canonical bounded graded-piece computation"]
theorem canonicalFacIso_inv_naturality
    (p : ℤ) {K L : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (Bounded.GradedPiece.homotopy C p).map f ≫
        (Bounded.GradedPiece.canonicalFacIso C p).inv.app L =
      (Bounded.GradedPiece.canonicalFacIso C p).inv.app K ≫
        (Bounded.GradedPiece.canonicalLift C p).map
          ((Bounded.Quotient.canonicalFunctor C).map f) := sorry

end Bounded.GradedPiece.Computation

end CategoryTheory.FilteredObject.FiniteDerived
