module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Alteration
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.RingHom.Fiber.Map

/-!
# Local ring-theoretic consequences of regular alterations

A local Noetherian domain admitting an algebraic-space alteration from a regular
integral source has a regular principal localization, finite normalization, normal
completions of that normalization, and a regular generic formal fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsAlteration

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
variable (X : AlgebraicSpace (Spec (.of A))) [IsIntegral X]
variable (f : X ⟶ specSpace A) [IsAlteration f] [IsRegular X]

include X f

/-- A local Noetherian domain admitting an alteration from a regular integral algebraic space
has a nonzero principal localization that is regular. -/
theorem exists_regularLocalization :
    ∃ a : A, a ≠ 0 ∧ IsRegularRing (Localization.Away a) :=
  sorry

/-- A local Noetherian domain admitting an alteration from a regular integral algebraic space
has finite integral closure in its fraction field. -/
theorem isN1Ring : IsN1Ring A :=
  sorry

/-- The completion of the normalization of a local Noetherian domain along its extended maximal
ideal is normal when the domain admits an alteration from a regular integral algebraic space. -/
theorem isNormalRing_adicCompletion :
    let B := integralClosure A (FractionRing A)
    IsNormalRing (AdicCompletion (Ideal.map (algebraMap A B) (maximalIdeal A)) B) :=
  sorry

/-- Every completed local ring of the normalization at a maximal ideal is normal when the
local Noetherian domain admits an alteration from a regular integral algebraic space. -/
theorem isNormalRing_completedLocalRing :
    let B := integralClosure A (FractionRing A)
    ∀ n : MaximalSpectrum B,
      IsNormalRing (PrimeSpectrum.CompletedLocalRing n.toPrimeSpectrum) :=
  sorry

/-- The generic formal fibre of a local Noetherian domain admitting an alteration from a regular
integral algebraic space is a regular ring. -/
theorem isRegularRing_genericFormalFiber :
    IsRegularRing ((algebraMap A (AdicCompletion (maximalIdeal A) A)).Fiber (⊥ : Ideal A)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsAlteration
