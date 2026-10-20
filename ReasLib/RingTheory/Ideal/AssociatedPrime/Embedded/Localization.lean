module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded.Quotient

@[expose] public section

/-!
# Localizing the Quotient without Embedded Primes

@stack 02M7
-/

universe u v

namespace Module.embeddedPrimeFreeSubmodule

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The canonical nowhere-dense submodule commutes with localization away from an element. -/
@[stacks 02M7 "localization of the canonical nowhere-dense submodule"]
theorem localized_away_eq (f : R) :
    (Module.embeddedPrimeFreeSubmodule R M).localized (.powers f) =
      Module.embeddedPrimeFreeSubmodule (Localization.Away f) (LocalizedModule.Away f M) := sorry

/-- Localizing the embedded-prime-free quotient agrees with taking the embedded-prime-free
quotient after localization. -/
@[stacks 02M7 "localization of the embedded-prime-free quotient"]
noncomputable def awayQuotientEquiv (f : R) :
    LocalizedModule.Away f (M ⧸ Module.embeddedPrimeFreeSubmodule R M) ≃ₗ[Localization.Away f]
      LocalizedModule.Away f M ⧸
        Module.embeddedPrimeFreeSubmodule (Localization.Away f) (LocalizedModule.Away f M) :=
  (localizedQuotientEquiv (.powers f) (Module.embeddedPrimeFreeSubmodule R M)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (localized_away_eq R M f)

end Module.embeddedPrimeFreeSubmodule
