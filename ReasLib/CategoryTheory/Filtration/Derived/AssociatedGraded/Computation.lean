/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of the finite associated-graded derived comparison

The associated-graded localization lift is defined in `Derived.AssociatedGraded`.  This leaf owns
the forward and inverse naturality equations used when calculating its action on maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.Computation

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]

/-- Naturality of the forward finite associated-graded factorization comparison. -/
@[reassoc (attr := simp), stacks 05S3 "finite associated-graded derived computation"]
theorem facIso_hom_naturality
    (h_inverts : AssociatedGraded.Inverts C)
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (AssociatedGraded.lift C h_inverts).map ((Quotient.functor C).map f) ≫
        (AssociatedGraded.facIso C h_inverts).hom.app L =
      (AssociatedGraded.facIso C h_inverts).hom.app K ≫
        (AssociatedGraded.homotopy C).map f := sorry

/-- Naturality of the inverse finite associated-graded factorization comparison. -/
@[reassoc (attr := simp), stacks 05S3 "finite associated-graded derived computation"]
theorem facIso_inv_naturality
    (h_inverts : AssociatedGraded.Inverts C)
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (AssociatedGraded.homotopy C).map f ≫
        (AssociatedGraded.facIso C h_inverts).inv.app L =
      (AssociatedGraded.facIso C h_inverts).inv.app K ≫
        (AssociatedGraded.lift C h_inverts).map ((Quotient.functor C).map f) := sorry

/-- Naturality of the canonical forward finite associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S3 "canonical finite associated-graded derived computation"]
theorem canonicalFacIso_hom_naturality
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (AssociatedGraded.canonicalLift C).map ((Quotient.functor C).map f) ≫
        (AssociatedGraded.canonicalFacIso C).hom.app L =
      (AssociatedGraded.canonicalFacIso C).hom.app K ≫
        (AssociatedGraded.homotopy C).map f := sorry

/-- Naturality of the canonical inverse finite associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S3 "canonical finite associated-graded derived computation"]
theorem canonicalFacIso_inv_naturality
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (AssociatedGraded.homotopy C).map f ≫
        (AssociatedGraded.canonicalFacIso C).inv.app L =
      (AssociatedGraded.canonicalFacIso C).inv.app K ≫
        (AssociatedGraded.canonicalLift C).map ((Quotient.functor C).map f) := sorry

end CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.Computation
