/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalCohomology.Gorenstein
public import ReasLib.RingTheory.Catenary.Universally
public import ReasLib.RingTheory.FormalFiber.CohenMacaulay
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.Serre

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace Module.LocalCohomology

/-- For a universally catenary ring whose local formal fibers are Cohen--Macaulay,
local cohomology of a finite module is finite in every natural degree below its
possibly infinite cutoff. -/
theorem cohomology_finite_of_lt_cutoff_of_formalFibers
    {A M : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
    (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (h_formal : ∀ p : PrimeSpectrum A,
      FieldAlgebraProperty.cohenMacaulay.HoldsOnFormalFibers
        (Localization.AtPrime p.asIdeal)) :
    ∀ i : ℕ, (.some (i : ℕ∞) : WithBot ℕ∞) < cutoff I M →
      Module.Finite A
        (ModuleCat.SupportedOn.cohomology
          (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)) := sorry

/-- For a universally catenary ring whose local formal fibers are Cohen--Macaulay,
local cohomology of a finite module is not finite at a finite cutoff. -/
theorem cohomology_not_finite_of_cutoff_of_formalFibers
    {A M : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
    (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (s : ℕ) (hs : cutoff I M = (.some (s : ℕ∞) : WithBot ℕ∞))
    (h_formal : ∀ p : PrimeSpectrum A,
      FieldAlgebraProperty.cohenMacaulay.HoldsOnFormalFibers
        (Localization.AtPrime p.asIdeal)) :
    ¬ Module.Finite A
      (ModuleCat.SupportedOn.cohomology
        (PrimeSpectrum.zeroLocus (I : Set A))
      (ModuleCat.single0 (ModuleCat.of A M)) (s : ℤ)) := sorry

/-- For a universally catenary ring whose formal fibers satisfy the Serre
condition `(S_n)`, local cohomology of a finite module is finite in every
degree at most `n` when `n` is below the cutoff. -/
theorem cohomology_finite_of_le_cutoff_of_serreFormalFibers
    {A M : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
    (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (n : ℕ) (h_cutoff : (.some (n : ℕ∞) : WithBot ℕ∞) < cutoff I M)
    (h_formal : ∀ p : PrimeSpectrum A,
      (FieldAlgebraProperty.serreConditionS n).HoldsOnFormalFibers
        (Localization.AtPrime p.asIdeal)) :
    ∀ i : ℕ, i ≤ n →
      Module.Finite A
        (ModuleCat.SupportedOn.cohomology
          (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)) := sorry

/-- For a universally catenary ring whose formal fibers satisfy the Serre
condition `(S_{s - 1})`, local cohomology of a finite module is not finite in
degree `s` when the cutoff is the finite value `s`. -/
theorem cohomology_not_finite_of_cutoff_of_serreFormalFibers
    {A M : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
    (I : Ideal A) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (s : ℕ) (hs : cutoff I M = (.some (s : ℕ∞) : WithBot ℕ∞))
    (h_formal : ∀ p : PrimeSpectrum A,
      (FieldAlgebraProperty.serreConditionS (s - 1)).HoldsOnFormalFibers
        (Localization.AtPrime p.asIdeal)) :
    ¬ Module.Finite A
      (ModuleCat.SupportedOn.cohomology
        (PrimeSpectrum.zeroLocus (I : Set A))
        (ModuleCat.single0 (ModuleCat.of A M)) (s : ℤ)) := sorry

end Module.LocalCohomology
