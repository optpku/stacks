module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Depth

@[expose] public section

/-!
# Cohen-Macaulay Modules

A finite module over a Noetherian local ring is Cohen-Macaulay if its depth equals the Krull
dimension of its support.

## Main definitions

* `Module.CohenMacaulay` — the local CM condition (depth = support dimension).
* `Module.LocallyCohenMacaulay` — the global CM condition (CM at all primes).

@stack 00N3
@stack 0AAH
-/

universe u v

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-- A finite module over a Noetherian local ring is Cohen-Macaulay when the Krull dimension of
its support equals its depth. -/
@[stacks 00N3]
class CohenMacaulay (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop extends Module.Finite R M where
  supportDim_eq_moduleDepth : supportDim R M = .some (moduleDepth R M)

/-- A module is Cohen-Macaulay exactly when it is finite and its support dimension equals its
depth. -/
theorem cohenMacaulay_iff :
    CohenMacaulay R M ↔ Module.Finite R M ∧ supportDim R M = .some (moduleDepth R M) := sorry

/-- Every field is Cohen-Macaulay as a module over itself. -/
instance CohenMacaulay.selfOfField (K : Type u) [Field K] : CohenMacaulay K K := sorry

end Module

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-- A finite module over a Noetherian ring is Cohen-Macaulay if, for every prime `𝔭`, the
localization `M_𝔭` is a Cohen-Macaulay module over `R_𝔭`. -/
@[stacks 0AAH]
class LocallyCohenMacaulay (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop extends Module.Finite R M where
  localizedModule_cohenMacaulay :
    ∀ p : PrimeSpectrum R,
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)

/-- A module is locally Cohen-Macaulay exactly when it is finite and every prime localization is
Cohen-Macaulay. -/
theorem locallyCohenMacaulay_iff :
    LocallyCohenMacaulay R M ↔
      Module.Finite R M ∧
        ∀ p : PrimeSpectrum R,
          Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M) := sorry

/-- Every field is locally Cohen-Macaulay as a module over itself. -/
instance LocallyCohenMacaulay.selfOfField (K : Type u) [Field K] :
    LocallyCohenMacaulay K K := sorry

end Module

end
