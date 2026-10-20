module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude

/-!
# Shifts and Tor-amplitude

@stack 08G2

Cohomological shift translates both endpoints of a Tor-amplitude interval.  In particular,
finite Tor dimension is stable under every integral shift.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.DerivedTensor

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ (K L : CochainComplex C ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]
variable [Right.Has (C := C)]

/-- Shifting a derived object translates its lower Tor-amplitude bound. -/
@[stacks 08G2 "lower Tor-amplitude under shift"]
theorem hasTorAmplitudeGE_shift_iff (K : DerivedCategory C) (n a : ℤ) :
    HasTorAmplitudeGE (K⟦n⟧) a ↔ HasTorAmplitudeGE K (a + n) := sorry
/- Proof strategy: apply the t-structure identity for `IsGE` under cohomological shift to every
degree-zero tensor test, using the shift compatibility of fixed-right derived tensor. -/

/-- Shifting a derived object translates its upper Tor-amplitude bound. -/
@[stacks 08G2 "upper Tor-amplitude under shift"]
theorem hasTorAmplitudeLE_shift_iff (K : DerivedCategory C) (n b : ℤ) :
    HasTorAmplitudeLE (K⟦n⟧) b ↔ HasTorAmplitudeLE K (b + n) := sorry
/- Proof strategy: apply the t-structure identity for `IsLE` under cohomological shift to every
degree-zero tensor test, using the shift compatibility of fixed-right derived tensor. -/

/-- Shifting a derived object translates both endpoints of its Tor-amplitude interval. -/
@[stacks 08G2 "Tor-amplitude interval under shift"]
theorem hasTorAmplitudeIn_shift_iff (K : DerivedCategory C) (n a b : ℤ) :
    HasTorAmplitudeIn (K⟦n⟧) a b ↔ HasTorAmplitudeIn K (a + n) (b + n) := sorry
/- Proof strategy: combine `hasTorAmplitudeGE_shift_iff` and `hasTorAmplitudeLE_shift_iff` through
`hasTorAmplitudeIn_iff`. -/

/-- Finite Tor dimension is invariant under cohomological shift. -/
@[stacks 08G2 "finite Tor dimension under shift"]
theorem hasFiniteTorDimension_shift_iff (K : DerivedCategory C) (n : ℤ) :
    HasFiniteTorDimension (K⟦n⟧) ↔ HasFiniteTorDimension K := sorry
/- Proof strategy: unfold finite Tor dimension as existence of an interval and translate its two
endpoints with `hasTorAmplitudeIn_shift_iff`; use the inverse shift for the converse. -/

/-- Finite Tor dimension is stable under all integral shifts. -/
@[stacks 08G2 "finite Tor dimension is shift-stable"]
instance finiteTorDimension_isStableUnderShift :
    (finiteTorDimension (C := C)).IsStableUnderShift ℤ := sorry
/- Proof strategy: package `hasFiniteTorDimension_shift_iff` as the required object-property
shift-stability instance. -/

end

end CategoryTheory.DerivedCategory.DerivedTensor
