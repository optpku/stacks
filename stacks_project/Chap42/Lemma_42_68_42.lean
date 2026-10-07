module

import StacksCheckRecall
public import ReasLib.RingTheory.Module.Support.PrimeSpan

universe u v

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 42.68.42: at a minimal point of the support, a finite module admits a finite family
whose terminal span quotient avoids that point, whose successive span quotients are copies of
the corresponding prime quotient, and whose cardinality is the localized length. -/
@[stacks 02QC] #check
  (Module.PrimeSpan.exists_of_minimalSupport :
    ∀ (q : PrimeSpectrum R), Minimal (· ∈ Module.support R M) q →
      ∃ l : ℕ, ∃ x : Fin l → M,
        q ∉ Module.support R (M ⧸ Submodule.span R (Set.range x)) ∧
          (∀ i : Fin l,
            Nonempty
              ((Submodule.span R (x '' Set.Iic i) ⧸
                  (Submodule.span R (x '' Set.Iio i)).submoduleOf
                    (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
                R ⧸ q.asIdeal)) ∧
          (l : ℕ∞) = Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule.AtPrime q.asIdeal M))

/- The cardinality conclusion only needs the terminal support and successive-factor
hypotheses. -/
#check
  (Module.PrimeSpan.card_eq_localizedLength :
    ∀ (q : PrimeSpectrum R) (l : ℕ) (x : Fin l → M),
      q ∉ Module.support R (M ⧸ Submodule.span R (Set.range x)) →
        (∀ i : Fin l,
          Nonempty
            ((Submodule.span R (x '' Set.Iic i) ⧸
                (Submodule.span R (x '' Set.Iio i)).submoduleOf
                  (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
              R ⧸ q.asIdeal)) →
        (l : ℕ∞) = Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal M))

end Module
