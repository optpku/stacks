module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteForget
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclic Finite Filtered Complexes

This module identifies the homology-package-neutral acyclic predicate for finite filtered
complexes with Mathlib's abelian homotopy-category presentation.  It is a separate layer so the
basic finite-complex API retains its minimal homology assumptions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A finite filtered complex whose associated graded is acyclic has acyclic underlying complex. -/
@[stacks 05RZ "finite filtered acyclic forgetful bridge"]
theorem Finite.Acyclic.forget_of_associatedGraded
    {L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hL : ((Finite.AssociatedGraded.cochain C).obj L).Acyclic) :
    (Finite.Forget.cochain C).obj L |>.Acyclic := sorry

namespace Finite.Forget.Homotopy.Acyclic

/-- A finite filtered acyclic homotopy object remains acyclic after forgetting its filtration. -/
@[stacks 05RZ "finite filtered acyclic forgetful bridge"]
theorem map
    (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ))
    (hK : FilteredObject.Finite.Homotopy.acyclic C K) :
    HomotopyCategory.subcategoryAcyclic C ((Finite.Forget.homotopy C).obj K) := sorry

end Finite.Forget.Homotopy.Acyclic

/-- For graded objects in an abelian category, vanishing in every homology degree is exactly
membership in the canonical acyclic homotopy subcategory. -/
@[stacks 05RZ "finite filtered associated graded acyclic complex"]
theorem Finite.Acyclic.associatedGraded_eq_subcategory :
    HomotopyCategory.Homology.acyclic (GradedObject ℤ C) =
      HomotopyCategory.subcategoryAcyclic (GradedObject ℤ C) := sorry

/-- A finite filtered complex is acyclic exactly when its associated graded image belongs to
Mathlib's canonical abelian acyclic homotopy subcategory. -/
@[stacks 05RZ "finite filtered acyclic complex"]
theorem Finite.Acyclic.iff_subcategory
    (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :
    FilteredObject.Finite.Homotopy.acyclic C K ↔
      HomotopyCategory.subcategoryAcyclic (GradedObject ℤ C)
        ((Finite.AssociatedGraded.homotopy C).obj K) := sorry

end CategoryTheory.FilteredObject
