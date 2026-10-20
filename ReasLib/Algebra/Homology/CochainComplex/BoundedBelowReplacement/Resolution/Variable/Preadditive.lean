module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Plus.Localization.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive Variable-Lower-Bound Localizers

The variable-lower-bound localizer is a composite of the termwise full-subcategory localizer and
the bounded-below inclusion localizer. This leaf exposes its additive structure as a stable
instance for the map calculus on resolutions.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Plus.TermsIn

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]

/-- The functor underlying the variable-lower-bound termwise localizer is additive. -/
@[stacks 05T6 "additivity of the variable-lower-bound localizer"]
instance localizerFunctorAdditive (P : ObjectProperty A) :
    (localizer P).functor.Additive := sorry

variable (P : ObjectProperty A)

end CochainComplex.Plus.TermsIn
