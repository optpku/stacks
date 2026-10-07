module

public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of finite derived graded-piece comparisons

Each graded piece is obtained by evaluating the associated-graded lift.  The factorization
comparison is nevertheless exposed here so downstream map calculations do not have to unfold the
three-stage composite by hand.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.Computation

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]

/-- Naturality of the forward finite derived graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S3 "finite derived graded-piece computation"]
theorem facIso_hom_naturality
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ)
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (GradedPiece.lift C h_inverts p).map ((Quotient.functor C).map f) ≫
        (GradedPiece.facIso C h_inverts p).hom.app L =
      (GradedPiece.facIso C h_inverts p).hom.app K ≫
        (GradedPiece.homotopy C p).map f := sorry

/-- Naturality of the inverse finite derived graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S3 "finite derived graded-piece computation"]
theorem facIso_inv_naturality
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ)
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (GradedPiece.homotopy C p).map f ≫
        (GradedPiece.facIso C h_inverts p).inv.app L =
      (GradedPiece.facIso C h_inverts p).inv.app K ≫
        (GradedPiece.lift C h_inverts p).map ((Quotient.functor C).map f) := sorry

/-- Naturality of the canonical forward finite derived graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S3 "canonical finite derived graded-piece computation"]
theorem canonicalFacIso_hom_naturality
    (p : ℤ)
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (GradedPiece.canonicalLift C p).map ((Quotient.functor C).map f) ≫
        (GradedPiece.canonicalFacIso C p).hom.app L =
      (GradedPiece.canonicalFacIso C p).hom.app K ≫
        (GradedPiece.homotopy C p).map f := sorry

/-- Naturality of the canonical inverse finite derived graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S3 "canonical finite derived graded-piece computation"]
theorem canonicalFacIso_inv_naturality
    (p : ℤ)
    {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)} (f : K ⟶ L) :
    (GradedPiece.homotopy C p).map f ≫
        (GradedPiece.canonicalFacIso C p).inv.app L =
      (GradedPiece.canonicalFacIso C p).inv.app K ≫
        (GradedPiece.canonicalLift C p).map ((Quotient.functor C).map f) := sorry

end CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.Computation
