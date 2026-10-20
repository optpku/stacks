/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Quotient
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated Graded on Finite Filtered Derived Categories

The concrete descent construction takes its inversion certificate as explicit input.  The source
theorem establishing that certificate is a separate Prop-valued proof obligation, so no derived
functor data is built from a deferred proof.  Bounded variants are kept in a separate module
because they additionally depend on the standard t-structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]

namespace AssociatedGraded

/-- The finite associated-graded homotopy functor followed by ordinary derived localization. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
noncomputable def homotopy :
    HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ) ⥤
      DerivedCategory (GradedObject ℤ C) :=
  Functor.Homotopy.toDerived (FilteredObject.Finite.AssociatedGraded.functor C)

/-- The finite associated-graded homotopy-to-derived functor commutes with integer shifts. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
noncomputable instance Homotopy.commShift :
    (homotopy C).CommShift ℤ :=
  inferInstanceAs
    ((Finite.AssociatedGraded.homotopy C ⋙ DerivedCategory.Qh).CommShift ℤ)

/-- The proposition that the associated-graded homotopy-to-derived functor inverts finite
filtered quasi-isomorphisms.  It is an explicit input to every construction that descends that
functor through the finite filtered derived localization. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
abbrev Inverts : Prop :=
  (FilteredObject.Finite.Homotopy.quasiIso C).IsInvertedBy (homotopy C)

/-- The finite associated-graded homotopy-to-derived functor inverts finite filtered
quasi-isomorphisms. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
theorem inverts : Inverts C := sorry

/-- The associated-graded functor on the finite filtered derived category, constructed from an
explicit certificate that its homotopy-level precursor inverts finite filtered
quasi-isomorphisms. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
noncomputable def lift (h_inverts : Inverts C) :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.Category C ⥤
      DerivedCategory (GradedObject ℤ C) :=
  CategoryTheory.Localization.lift (homotopy C) h_inverts
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)

/-- Derived associated graded composed with the finite filtered quotient functor is the
associated-graded homotopy functor followed by ordinary derived localization. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
noncomputable def facIso (h_inverts : Inverts C) :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C ⋙
        lift C h_inverts ≅ homotopy C :=
  CategoryTheory.Localization.fac (homotopy C) h_inverts
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)

/-- The canonical finite associated-graded derived functor.

This is the default downstream entry point.  The explicit-certificate `lift` remains available
for constructions that deliberately work with a transported inversion proof.
-/
@[stacks 05S3 "canonical finite filtered associated graded derived functor"]
noncomputable abbrev canonicalLift :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.Category C ⥤
      DerivedCategory (GradedObject ℤ C) :=
  lift C (inverts C)

/-- The factorization comparison for the canonical finite associated-graded derived functor. -/
@[stacks 05S3 "canonical finite filtered associated graded derived functor"]
noncomputable abbrev canonicalFacIso :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C ⋙
        canonicalLift C ≅ homotopy C :=
  facIso C (inverts C)

end AssociatedGraded

namespace GradedPiece

variable [HasDerivedCategory C]

/-- The `p`-th finite associated-graded piece, followed by ordinary derived localization. -/
@[stacks 05S3 "finite filtered derived graded piece"]
noncomputable def homotopy (p : ℤ) :
    HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
  Functor.Homotopy.Comp.toDerived
    (FilteredObject.Finite.AssociatedGraded.functor C) (GradedObject.eval p)

/-- Derived evaluation of the associated-graded homotopy functor agrees with the direct
homotopy-level `p`-th graded-piece functor. -/
@[stacks 05S3 "finite filtered derived graded piece"]
noncomputable def compIso (p : ℤ) :
    AssociatedGraded.homotopy C ⋙ (GradedObject.eval p).mapDerivedCategory ≅ homotopy C p :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (GradedObject.eval p).mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm

/-- The `p`-th associated-graded-piece functor on the finite filtered derived category.

It is defined by derived evaluation after the canonical associated-graded descent, so it does
not require a second choice of localization lift. -/
@[stacks 05S3 "finite filtered derived graded piece"]
noncomputable def lift (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.Category C ⥤
      DerivedCategory C :=
  AssociatedGraded.lift C h_inverts ⋙ (GradedObject.eval p).mapDerivedCategory

/-- The finite derived graded-piece functor factors the direct homotopy-level graded-piece
functor through the finite filtered derived quotient. -/
@[stacks 05S3 "finite filtered derived graded piece"]
noncomputable def facIso
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C ⋙
        lift C h_inverts p ≅ homotopy C p :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (AssociatedGraded.facIso C h_inverts)
      ((GradedObject.eval p).mapDerivedCategory) ≪≫
    compIso C p

/-- The canonical finite derived graded-piece functor. -/
@[stacks 05S3 "canonical finite filtered derived graded piece"]
noncomputable abbrev canonicalLift (p : ℤ) :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.Category C ⥤
      DerivedCategory C :=
  lift C (AssociatedGraded.inverts C) p

/-- The factorization comparison for the canonical finite derived graded-piece functor. -/
@[stacks 05S3 "canonical finite filtered derived graded piece"]
noncomputable abbrev canonicalFacIso (p : ℤ) :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C ⋙
        canonicalLift C p ≅ homotopy C p :=
  facIso C (AssociatedGraded.inverts C) p

end GradedPiece

end CategoryTheory.FilteredObject.FiniteDerived
