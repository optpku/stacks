module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.Algebra.Module.CompositionSeries.Factor

/-!
# Localized lengths of composition factors

The multiplicity of a maximal ideal in a composition series is intrinsic: it
is the length of the localized module.  The bundled maximal-spectrum statement
is the canonical API; the ideal-valued statement is retained as a compatibility
bridge for existing localization code.

@stack 00J3
-/

@[expose] public section

open scoped BigOperators

universe u v

namespace Module.CompositionSeries

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.52.11 (4) (00J3): the multiplicity of a maximal ideal among the composition
factors equals the length of the localized module. -/
@[stacks 00J3 "(4)"]
theorem multiplicity_eq_length_localized
    (s : CompositionSeries (Submodule R M)) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤)
    (m : MaximalSpectrum R) :
    (multiplicity s m : ℕ∞) =
      Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal M) := sorry

/-- The local lengths of a finite-length composition series have finite support on the maximal
spectrum. This is the support statement underlying all enumeration-free localization formulas. -/
@[stacks 00J3 "finite support of localized composition-series lengths"]
theorem localizedLength_hasFiniteSupport
    (s : CompositionSeries (Submodule R M)) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤) :
    (fun m : MaximalSpectrum R ↦
      Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal M)).HasFiniteSupport := sorry

/-- A weighted sum over composition factors can be regrouped over the maximal spectrum without
choosing an enumeration of its points. -/
@[stacks 00J3 "weighted composition-factor localization finsum"]
theorem sum_factorWeight_eq_finsum_mul_length_localized
    (s : CompositionSeries (Submodule R M)) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤)
    (w : MaximalSpectrum R → ℕ∞) :
    ∑ i : Fin s.length, w (Factor.annihilatorPoint s i) =
      ∑ᶠ m : MaximalSpectrum R,
        w m * Module.length (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal M) := sorry

/-- A weighted sum over composition factors can be regrouped by annihilator point, with each
multiplicity replaced by the length of the corresponding localization. -/
@[stacks 00J3 "weighted composition-factor localization formula"]
theorem sum_factorWeight_eq_sum_mul_length_localized
    [Fintype (MaximalSpectrum R)]
    (s : CompositionSeries (Submodule R M)) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤)
    (w : MaximalSpectrum R → ℕ∞) :
    ∑ i : Fin s.length, w (Factor.annihilatorPoint s i) =
      ∑ m : MaximalSpectrum R,
        w m * Module.length (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal M) := sorry

end Module.CompositionSeries
