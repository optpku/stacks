module

public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Depth.Equiv
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local Bridges for Cohen-Macaulay Modules

Transport under linear equivalence and the comparison between local and primewise
Cohen-Macaulayness.

@stack 0AAG
@stack 00RG
-/

universe u v w

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module.CohenMacaulay

/-- Cohen-Macaulayness is preserved by an `R`-linear equivalence over a Noetherian local ring. -/
theorem of_linearEquiv [IsLocalRing R] {N : Type w} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [h : Module.CohenMacaulay R M] :
    Module.CohenMacaulay R N := sorry

/-- A finite module with zero support dimension over a Noetherian local ring is
Cohen-Macaulay. -/
theorem of_supportDim_eq_zero [IsLocalRing R] [Module.Finite R M]
    (hdim : Module.supportDim R M = 0) :
    Module.CohenMacaulay R M := sorry

/-- A Noetherian local ring of Krull dimension zero is Cohen--Macaulay as its
self-module.  The general finite-module construction is
`Module.CohenMacaulay.of_supportDim_eq_zero`; this theorem supplies the
self-module dimension bridge used by local algebra applications. -/
@[stacks 00RG "zero-dimensional local rings are Cohen--Macaulay"]
theorem self_of_ringKrullDim_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 0) :
    Module.CohenMacaulay R R := sorry

/-- A Noetherian local ring with Krull dimension at most zero is
Cohen--Macaulay as its self-module.  This class-oriented form is convenient
when the dimension bound is already available to typeclass search. -/
@[stacks 00RG "zero-dimensional local rings are Cohen--Macaulay"]
theorem self_of_krullDimLE_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 0 R] :
    Module.CohenMacaulay R R := sorry

/-- Localizing a Cohen--Macaulay module at a prime in its support remains
Cohen--Macaulay. -/
@[stacks 0AAG]
theorem localizedModule_atPrime [IsLocalRing R] [Module.CohenMacaulay R M]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := sorry

/-- Localizing a Cohen--Macaulay module at any prime either preserves
Cohen--Macaulayness or produces the zero module. -/
@[stacks 0AAG "including the zero localization"]
theorem localizedModule_atPrime_or_subsingleton
    [IsLocalRing R] [Module.CohenMacaulay R M] (p : PrimeSpectrum R) :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) ∨
      Subsingleton (LocalizedModule.AtPrime p.asIdeal M) := by
  by_cases hp : p ∈ Module.support R M
  · exact Or.inl (localizedModule_atPrime p hp)
  · exact Or.inr (Module.notMem_support_iff.mp hp)

end Module.CohenMacaulay

namespace Module.LocallyCohenMacaulay

/-- A locally Cohen-Macaulay module has full support. -/
theorem support_eq_univ (h : Module.LocallyCohenMacaulay R M) :
    Module.support R M = Set.univ := sorry

/-- Local Cohen-Macaulayness is preserved by an `R`-linear equivalence. -/
theorem of_linearEquiv {N : Type w} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [h : Module.LocallyCohenMacaulay R M] :
    Module.LocallyCohenMacaulay R N := sorry

/-- Over a Noetherian local ring, a locally Cohen-Macaulay module is Cohen-Macaulay. -/
theorem toCohenMacaulay [IsLocalRing R] (h : Module.LocallyCohenMacaulay R M) :
    Module.CohenMacaulay R M := sorry

end Module.LocallyCohenMacaulay

namespace Module

/-- Over a Noetherian local ring, local Cohen-Macaulayness supplies a Cohen-Macaulay instance. -/
instance cohenMacaulay_of_locallyCohenMacaulay [IsLocalRing R]
    [h : Module.LocallyCohenMacaulay R M] :
    Module.CohenMacaulay R M := sorry

/-- Over a Noetherian local ring, a Cohen-Macaulay module with full support is locally
Cohen-Macaulay. -/
theorem locallyCohenMacaulay_of_cohenMacaulay [IsLocalRing R] [Module.CohenMacaulay R M]
    (hsupp : Module.support R M = Set.univ) :
    Module.LocallyCohenMacaulay R M := sorry

end Module

end
