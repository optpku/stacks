module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration.RegularSource
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Regular.JRing
public import ReasLib.RingTheory.RingHom.Fiber.Map

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsAlteration

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
variable (X : Scheme.{u}) [IsIntegral X]
variable (π : X ⟶ Spec (.of A)) [IsAlteration π] [Scheme.Regular X]

include X π

/-- A local Noetherian domain admitting an alteration from a regular integral scheme has a
nonzero principal localization that is regular. -/
theorem exists_regularLocalization :
    ∃ a : A, a ≠ 0 ∧ IsRegularRing (Localization.Away a) := sorry

/-- A local Noetherian domain admitting an alteration from a regular integral scheme is an
N-1 ring. -/
theorem isN1Ring : IsN1Ring A := sorry

/-- The completion of the normalization of a local Noetherian domain along its extended maximal
ideal is a normal ring when the domain admits a regular alteration. -/
theorem isNormalRing_adicCompletion :
    let B := integralClosure A (FractionRing A)
    IsNormalRing
      (AdicCompletion (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B) := sorry

/-- Every completed local ring of the normalization at a maximal ideal is normal under a regular
alteration of a local Noetherian domain. -/
theorem isNormalRing_completedLocalRing :
    let B := integralClosure A (FractionRing A)
    ∀ n : MaximalSpectrum B,
      IsNormalRing (PrimeSpectrum.CompletedLocalRing n.toPrimeSpectrum) := sorry

/-- The generic formal fiber of a local Noetherian domain admitting a regular alteration is a
regular ring. -/
theorem isRegularRing_genericFormalFiber :
    IsRegularRing
      ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)).Fiber
        (⊥ : Ideal A)) := sorry

end AlgebraicGeometry.IsAlteration
