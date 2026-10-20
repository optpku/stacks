module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus.Localization.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive Variable-Upper-Bound Localizers

The variable-upper-bound localizer is a composite of the termwise full-subcategory localizer and
the bounded-above inclusion localizer. This leaf exposes its additive structure as a stable
instance for the map calculus on resolutions.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Minus.TermsIn

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]

/-- The functor underlying the variable-upper-bound termwise localizer is additive. -/
@[stacks 0643 "additivity of the variable-upper-bound localizer"]
instance localizerFunctorAdditive (P : ObjectProperty A) :
    (localizer P).functor.Additive := sorry

variable (P : ObjectProperty A)

end CochainComplex.Minus.TermsIn
