module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import ReasLib.RingTheory.Localization.FractionRing.SubringPair

/-!
# One-dimensional fraction-subring pairs

This file records localization and tensor-product results for Noetherian
semilocal one-dimensional subrings of a common fraction field, including the
dichotomy when one component is a discrete valuation ring.
-/

@[expose] public section

universe u

namespace FractionRing.SubringPair

variable {K : Type u} [Field K]

variable (P : FractionRing.SubringPair K)
variable [IsNoetherianRing P.left] [Finite (MaximalSpectrum P.left)]

section discreteValuation

variable [IsDiscreteValuationRing P.right]

/-- If some unit of the left component is outside the intersection, the two
components are localizations away from elements of the intersection which
together generate the unit ideal. -/
theorem exists_awayCover_of_unit_not_mem_intersection
    (hdim : ringKrullDim P.left = 1)
    (hunit : ∃ u : P.leftˣ, ((u : P.left) : K) ∉ P.intersection) :
    ∃ u x : P.intersection,
      ∃ hleft : IsLocalization.Away u P.left,
        ∃ hright : IsLocalization.Away x P.right,
          Ideal.span ({u, x} : Set P.intersection) = ⊤ := sorry

/-- If some unit of the left component is outside the intersection, the
canonical tensor comparison from the two components to their common fraction
field is bijective. -/
theorem tensorToAmbient_bijective_of_unit_not_mem_intersection
    (hdim : ringKrullDim P.left = 1)
    (hunit : ∃ u : P.leftˣ, ((u : P.left) : K) ∉ P.intersection) :
    Function.Bijective P.tensorToAmbient := sorry

/-- If every unit of the left component belongs to the intersection, the
right valuation subring dominates the localization of the left component at
some maximal ideal. -/
theorem exists_dominated_localization_of_units_mem_intersection
    (hdim : ringKrullDim P.left = 1)
    (hunit : ∀ u : P.leftˣ, ((u : P.left) : K) ∈ P.intersection) :
    ∃ m : MaximalSpectrum P.left,
      LocalSubring.ofPrime P.left m.asIdeal ≤ LocalSubring.range P.right.subtype := sorry

/-- If every unit of the left component belongs to the intersection, the
canonical tensor comparison from the two components to their common fraction
field is not surjective. -/
theorem tensorToAmbient_not_surjective_of_units_mem_intersection
    (hdim : ringKrullDim P.left = 1)
    (hunit : ∀ u : P.leftˣ, ((u : P.left) : K) ∈ P.intersection) :
    ¬ Function.Surjective P.tensorToAmbient := sorry

end discreteValuation

variable [IsNoetherianRing P.right] [Finite (MaximalSpectrum P.right)]

/-- If two Noetherian semilocal components of a fraction-subring pair have
Krull dimension one and their tensor comparison is surjective, they are away
localizations at elements which together generate the unit ideal. -/
theorem exists_awayCover_of_dim_one
    (hleft : ringKrullDim P.left = 1) (hright : ringKrullDim P.right = 1)
    (hsurj : Function.Surjective P.tensorToAmbient) :
    ∃ x y : P.intersection,
      IsLocalization.Away x P.left ∧ IsLocalization.Away y P.right ∧
        Ideal.span ({x, y} : Set P.intersection) = ⊤ := sorry

/-- For two Noetherian semilocal components of Krull dimension one,
surjectivity of the canonical tensor comparison to their common fraction
field implies its bijectivity. -/
theorem tensorToAmbient_bijective_of_dim_one
    (hleft : ringKrullDim P.left = 1) (hright : ringKrullDim P.right = 1)
    (hsurj : Function.Surjective P.tensorToAmbient) :
    Function.Bijective P.tensorToAmbient := sorry

end FractionRing.SubringPair
