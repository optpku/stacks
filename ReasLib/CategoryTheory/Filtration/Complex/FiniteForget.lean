/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetful functors for finite filtered complexes

This leaf contains the cochain-level and homotopy-level forgetful functors for finite filtered
complexes.  It deliberately stops before derived localization, so computations involving the
underlying complex do not require a chosen derived category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace Finite.Forget

/-- Forget the finite filtration termwise on cochain complexes. -/
@[stacks 05RZ "finite filtered cochain forgetful functor"]
noncomputable abbrev cochain :
    CochainComplex (FilteredObject.Finite.category C) ℤ ⥤ CochainComplex C ℤ :=
  (FilteredObject.Finite.Forget.functor C).mapHomologicalComplex (up ℤ)

/-- Forget the finite filtration after passing to the homotopy category. -/
@[stacks 05RZ "finite filtered homotopy forgetful functor"]
noncomputable def homotopy :
    HomotopyCategory (FilteredObject.Finite.category C) (up ℤ) ⥤
      HomotopyCategory C (up ℤ) :=
  (FilteredObject.Finite.Forget.functor C).mapHomotopyCategory (up ℤ)

namespace Homotopy

/-- The finite filtered forgetful homotopy functor carries the canonical shift comparison. -/
@[stacks 05RZ "finite filtered homotopy forgetful functor"]
noncomputable instance commShift :
    (homotopy C).CommShift ℤ :=
  inferInstanceAs (((FilteredObject.Finite.Forget.functor C).mapHomotopyCategory (up ℤ)).CommShift ℤ)

/-- The homotopy forgetful functor factors the cochain forgetful functor through the canonical
homotopy quotients. -/
@[stacks 05RZ "finite filtered homotopy forgetful functor"]
noncomputable def factors :
    HomotopyCategory.quotient (FilteredObject.Finite.category C) (up ℤ) ⋙
        homotopy C ≅
      cochain C ⋙ HomotopyCategory.quotient C (up ℤ) :=
  (FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryFactors (up ℤ)

namespace Quotient

/-- Computation of the finite filtered forgetful homotopy functor on a quotient object. -/
@[stacks 05RZ "finite filtered homotopy forgetful computation", simp]
theorem obj
    (K : CochainComplex (FilteredObject.Finite.category C) ℤ) :
    (homotopy C).obj
        ((HomotopyCategory.quotient (FilteredObject.Finite.category C) (up ℤ)).obj K) =
      (HomotopyCategory.quotient C (up ℤ)).obj
        ((cochain C).obj K) := sorry

/-- Computation of the finite filtered forgetful homotopy functor on a quotient morphism. -/
@[stacks 05RZ "finite filtered homotopy forgetful computation", simp]
theorem map
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ} (f : K ⟶ L) :
    (homotopy C).map
        ((HomotopyCategory.quotient (FilteredObject.Finite.category C) (up ℤ)).map f) =
      (HomotopyCategory.quotient C (up ℤ)).map
        ((cochain C).map f) := sorry

end Quotient

end Homotopy

end Finite.Forget

end CategoryTheory.FilteredObject
