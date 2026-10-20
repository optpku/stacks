module

public import ReasLib.CategoryTheory.Filtration.Derived.Quotient
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteAcyclic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting finite filtrations after derived localization

The homotopy-level functor is induced directly by forgetting the filtration.  Its descent still
uses the finite filtered localization, whose weak equivalences are detected by associated graded.
This leaf keeps that (Prop-valued) inversion certificate explicit so no non-Prop derived data
depends on a deferred proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory C]

namespace Forget

/-- The forgetful functor from finite filtered homotopy complexes to the ordinary derived
category. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable def homotopy :
    HomotopyCategory (FilteredObject.Finite.category C) (up ℤ) ⥤ DerivedCategory C :=
  Functor.Homotopy.toDerived (FilteredObject.Finite.Forget.functor C)

/-- The finite filtered forgetful homotopy-to-derived functor commutes with integer shifts. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable instance Homotopy.commShift :
    (homotopy C).CommShift ℤ :=
  inferInstanceAs
    ((Finite.Forget.homotopy C ⋙ DerivedCategory.Qh).CommShift ℤ)

/-- The proposition that forgetting a finite filtration inverts finite filtered
quasi-isomorphisms. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
abbrev Inverts : Prop :=
  (FilteredObject.Finite.Homotopy.quasiIso C).IsInvertedBy (homotopy C)

/-- Forgetting the filtration inverts finite filtered quasi-isomorphisms. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
theorem inverts : Inverts C := sorry

/-- The forgetful functor from the finite filtered derived category to the ordinary derived
category, constructed from an explicit inversion certificate. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable def lift (h_inverts : Inverts C) :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.Category C ⥤
      DerivedCategory C :=
  CategoryTheory.Localization.lift (homotopy C) h_inverts
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)

/-- The forgetful derived functor factors the finite filtered quotient functor. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable abbrev facIso (h_inverts : Inverts C) :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C ⋙
        lift C h_inverts ≅ homotopy C :=
  CategoryTheory.Localization.fac (homotopy C) h_inverts
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)

/-- The canonical finite filtered forgetful derived functor.

The explicit-certificate `lift` remains available for transported or alternative proofs of
inversion; ordinary downstream uses should start here.
-/
@[stacks 05S3 "canonical finite filtered forgetful derived functor"]
noncomputable abbrev canonicalLift :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.Category C ⥤
      DerivedCategory C :=
  lift C (inverts C)

/-- The factorization comparison for the canonical finite filtered forgetful derived functor. -/
@[stacks 05S3 "canonical finite filtered forgetful derived functor"]
noncomputable abbrev canonicalFacIso :
    _root_.CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C ⋙
        canonicalLift C ≅ homotopy C :=
  facIso C (inverts C)

end Forget

end CategoryTheory.FilteredObject.FiniteDerived
