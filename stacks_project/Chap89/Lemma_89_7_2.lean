module

public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Regular.JRing
public import ReasLib.RingTheory.RingHom.Fiber.Map
public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap72.Definition_72_8_3_Alteration
public import stacks_project.Chap89.Lemma_89_2_1

/-!
# Regular alterations of spectra imply local ring-theoretic consequences

A local Noetherian domain admitting an algebraic-space alteration from a
regular integral source has a regular principal localization, finite
normalization, normal completions of that normalization, and a regular
generic formal fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsAlteration

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
variable (X : AlgebraicSpace (Spec (.of A))) [IsIntegral X] [IsIntegral (specSpace A)]
variable (f : X ⟶ specSpace A) [IsAlteration f] [IsRegular X]

include X f

/-- Lemma 89.7.2 (1) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then there exists a
nonzero `a : A` such that `Localization.Away a` is a regular ring. -/
@[stacks 0BHU]
theorem exists_regularLocalization :
    ∃ a : A, a ≠ 0 ∧ IsRegularRing (Localization.Away a) :=
  sorry

/-- Lemma 89.7.2 (2) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then the integral
closure of `A` in its fraction field is finite over `A`. -/
@[stacks 0BHU]
theorem isN1Ring : IsN1Ring A :=
  sorry

/-- Lemma 89.7.2 (3) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then the 𝔪-adic
completion of the integral closure of `A` in its fraction field is a normal
ring. -/
@[stacks 0BHU]
theorem isNormalRing_adicCompletion :
    let B := integralClosure A (FractionRing A)
    IsNormalRing (AdicCompletion (Ideal.map (algebraMap A B) (maximalIdeal A)) B) :=
  sorry

/-- Lemma 89.7.2 (4) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then the completions of
the integral closure of `A` at its maximal ideals are normal domains. -/
@[stacks 0BHU]
theorem isNormalRing_completedLocalRing :
    let B := integralClosure A (FractionRing A)
    ∀ n : MaximalSpectrum B,
      IsNormalRing (PrimeSpectrum.CompletedLocalRing n.toPrimeSpectrum) :=
  sorry

/-- Lemma 89.7.2 (5) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then the generic formal
fibre of `A` is a regular ring. -/
@[stacks 0BHU]
theorem isRegularRing_genericFormalFiber :
    IsRegularRing ((algebraMap A (AdicCompletion (maximalIdeal A) A)).Fiber (⊥ : Ideal A)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsAlteration
