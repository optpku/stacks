/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Alteration.LocalConsequences
import StacksCheckRecall

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

/- Lemma 89.7.2 (1) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then there exists a
nonzero `a : A` such that `Localization.Away a` is a regular ring. -/
@[stacks 0BHU]
#check (AlgebraicGeometry.AlgebraicSpace.IsAlteration.exists_regularLocalization :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : AlgebraicSpace (Spec (.of A))) [IsIntegral X]
    (f : X ⟶ specSpace A) [IsAlteration f] [IsRegular X],
    ∃ a : A, a ≠ 0 ∧ IsRegularRing (Localization.Away a))

/- Lemma 89.7.2 (2) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then the integral
closure of `A` in its fraction field is finite over `A`. -/
@[stacks 0BHU]
#check (AlgebraicGeometry.AlgebraicSpace.IsAlteration.isN1Ring :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : AlgebraicSpace (Spec (.of A))) [IsIntegral X]
    (f : X ⟶ specSpace A) [IsAlteration f] [IsRegular X], IsN1Ring A)

/- Lemma 89.7.2 (3) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then the 𝔪-adic
completion of the integral closure of `A` in its fraction field is a normal
ring. -/
@[stacks 0BHU]
#check (AlgebraicGeometry.AlgebraicSpace.IsAlteration.isNormalRing_adicCompletion :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : AlgebraicSpace (Spec (.of A))) [IsIntegral X]
    (f : X ⟶ specSpace A) [IsAlteration f] [IsRegular X],
    let B := integralClosure A (FractionRing A)
    IsNormalRing (AdicCompletion (Ideal.map (algebraMap A B) (maximalIdeal A)) B))

/- Lemma 89.7.2 (3), maximal-local formulation. Let `(A, 𝔪, κ)` be a local
Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then the completions of
the integral closure of `A` at its maximal ideals are normal domains. -/
@[stacks 0BHU]
#check (AlgebraicGeometry.AlgebraicSpace.IsAlteration.isNormalRing_completedLocalRing :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : AlgebraicSpace (Spec (.of A))) [IsIntegral X]
    (f : X ⟶ specSpace A) [IsAlteration f] [IsRegular X],
    let B := integralClosure A (FractionRing A)
    ∀ n : MaximalSpectrum B,
      IsNormalRing (PrimeSpectrum.CompletedLocalRing n.toPrimeSpectrum))

/- Lemma 89.7.2 (4) Let `(A, 𝔪, κ)` be a local Noetherian domain. If there is
an alteration `f : X ⟶ specSpace A` with `X` regular, then the generic formal
fibre of `A` is a regular ring. -/
@[stacks 0BHU]
#check (AlgebraicGeometry.AlgebraicSpace.IsAlteration.isRegularRing_genericFormalFiber :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : AlgebraicSpace (Spec (.of A))) [IsIntegral X]
    (f : X ⟶ specSpace A) [IsAlteration f] [IsRegular X],
    IsRegularRing ((algebraMap A (AdicCompletion (maximalIdeal A) A)).Fiber (⊥ : Ideal A)))

end AlgebraicGeometry.AlgebraicSpace.IsAlteration
