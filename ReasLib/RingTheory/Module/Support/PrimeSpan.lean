/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.RingTheory.Module.Support.FiniteLength

@[expose] public section

universe u v

namespace Module.PrimeSpan

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The number of successive prime-quotient factors in a finite span filtration equals the
length of the module localized at that prime when the terminal quotient vanishes there. -/
theorem card_eq_localizedLength (q : PrimeSpectrum R) (l : ℕ) (x : Fin l → M)
    (h_support : q ∉ Module.support R (M ⧸ Submodule.span R (Set.range x)))
    (h_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (x '' Set.Iic i) ⧸
            (Submodule.span R (x '' Set.Iio i)).submoduleOf
              (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    (l : ℕ∞) = Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M) := sorry

/-- A finite module over a Noetherian ring admits, at each minimal point of its support, a
finite span filtration by copies of the corresponding prime quotient whose terminal quotient
vanishes at that point and whose cardinality is the localized length. -/
theorem exists_of_minimalSupport [IsNoetherianRing R] [Module.Finite R M]
    (q : PrimeSpectrum R) (h_min : Minimal (· ∈ Module.support R M) q) :
    ∃ l : ℕ, ∃ x : Fin l → M,
      q ∉ Module.support R (M ⧸ Submodule.span R (Set.range x)) ∧
        (∀ i : Fin l,
          Nonempty
            ((Submodule.span R (x '' Set.Iic i) ⧸
                (Submodule.span R (x '' Set.Iio i)).submoduleOf
                  (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
              R ⧸ q.asIdeal)) ∧
        (l : ℕ∞) = Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal M) := sorry

end Module.PrimeSpan
