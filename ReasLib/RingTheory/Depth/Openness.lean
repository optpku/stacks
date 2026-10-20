module

public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.RingTheory.Sequence.Regularity.Localization
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

open scoped ENat

universe u v

namespace Ideal

/-- Finite ideal-depth at a prime persists as a lower bound on a nonempty relatively open subset
of the closure of that prime in the prime spectrum. -/
theorem exists_open_depth_ge
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (hp : p ∈ PrimeSpectrum.zeroLocus (I : Set A))
    (e : ℕ)
    (hdepth : Ideal.depth (I.localizationAtPrime p)
      (LocalizedModule.AtPrime p.asIdeal M) = (e : ℕ∞)) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      (U ∩ PrimeSpectrum.zeroLocus p.asIdeal).Nonempty ∧
      ∀ q ∈ U ∩ PrimeSpectrum.zeroLocus p.asIdeal,
          (e : ℕ∞) ≤ Ideal.depth (I.localizationAtPrime q)
          (LocalizedModule.AtPrime q.asIdeal M) := sorry

end Ideal

namespace Module

/-- A finite module of finite depth at a prime has depth at least that value on
a nonempty relatively open subset of the prime's closure, with only finitely
many points where equality holds. -/
theorem exists_open_depth_ge_and_finite_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (e : ℕ)
    (hdepth : moduleDepth (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) = (e : ℕ∞)) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      (U ∩ PrimeSpectrum.zeroLocus p.asIdeal).Nonempty ∧
      (∀ q ∈ U ∩ PrimeSpectrum.zeroLocus p.asIdeal,
        (e : ℕ∞) ≤ moduleDepth (Localization.AtPrime q.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal M)) ∧
      Set.Finite {q ∈ U ∩ PrimeSpectrum.zeroLocus p.asIdeal |
        moduleDepth (Localization.AtPrime q.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal M) = (e : ℕ∞)} := sorry

end Module
