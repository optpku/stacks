module

public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Family

/-!
# Cardinally generated precoverages

This module records when every covering presieve is presented by a family whose index type is
small relative to a chosen cardinal.  It retains the chosen family data alongside the equivalent
cardinality formulation in terms of the raw presieve.
-/

@[expose] public section

open CategoryTheory

universe wκ v u

namespace CategoryTheory

namespace Presieve

variable {C : Type u} [Category.{v} C]

/-- A cardinal bound on the raw arrows of a presieve is equivalent to a cardinal bound on a
chosen generating family.  The latter presentation retains the cover index used by a source or
by later construction. -/
theorem hasGeneratingFamilyOfCardinalLT_iff
    {U : C} (R : Presieve U) (κ : Cardinal.{wκ}) :
    R.hasGeneratingFamilyOfCardinalLT κ ↔ HasCardinalLT R.uncurry κ := sorry

end Presieve

namespace Precoverage

variable {C : Type u} [Category.{v} C]

/-- Every covering presieve of `K` has raw arrow type of cardinality strictly below `κ`.  This is
the canonical cardinality condition on a precoverage and does not choose a presentation. -/
@[stacks 0GS0]
def hasCardinalLTCoveringPresieves (K : Precoverage C) (κ : Cardinal.{wκ}) : Prop :=
  ∀ ⦃U : C⦄ ⦃R : Presieve U⦄, R ∈ K U → HasCardinalLT R.uncurry κ

/-- Every covering presieve of `K` admits a generating family whose index type has cardinality
strictly below `κ`.  This is a presentation-dependent proposition, so it is an explicit
hypothesis rather than a typeclass. -/
def hasCardinalLTGeneratingFamilies (K : Precoverage C) (κ : Cardinal.{wκ}) : Prop :=
  ∀ ⦃U : C⦄ ⦃R : Presieve U⦄, R ∈ K U →
    R.hasGeneratingFamilyOfCardinalLT κ

/-- The source-style generating-family presentation is equivalent to the canonical raw-presieve
cardinality condition. -/
theorem hasCardinalLTGeneratingFamilies_iff
    (K : Precoverage C) (κ : Cardinal.{wκ}) :
    K.hasCardinalLTGeneratingFamilies κ ↔ K.hasCardinalLTCoveringPresieves κ := sorry

end Precoverage

namespace Coverage

variable {C : Type u} [Category.{v} C]

/-- The canonical raw-presieve cardinality condition for a coverage, viewed through its
underlying precoverage. -/
abbrev hasCardinalLTCoveringPresieves (K : Coverage C) (κ : Cardinal.{wκ}) : Prop :=
  K.toPrecoverage.hasCardinalLTCoveringPresieves κ

/-- The cardinally small generating-family condition for a coverage, viewed through its
underlying precoverage. -/
abbrev hasCardinalLTGeneratingFamilies (K : Coverage C) (κ : Cardinal.{wκ}) : Prop :=
  K.toPrecoverage.hasCardinalLTGeneratingFamilies κ

end Coverage

end CategoryTheory
