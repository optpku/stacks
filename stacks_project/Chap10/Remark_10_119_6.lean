module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Counterexample
public import ReasLib.RingTheory.LocalRing.Kollar.Determinantal
public import ReasLib.RingTheory.Spectrum.Maximal.Finite
public import stacks_project.Chap10.Example_10_119_5

/-!
# Iterated Finite Overrings of One-Dimensional Semilocal Domains

Starting from a nonregular maximal localization of a one-dimensional semilocal Noetherian domain,
one may repeatedly pass to a strict finite overring in the same fraction field. Nonreduced
completions yield sequences which never stabilize, while reduced maximal-local completions force
the procedure to stop.

@stack 00PC
-/

@[expose] public section

noncomputable section

universe u

open IsLocalRing

/-- A sequence of finite one-dimensional semilocal Noetherian overrings inside the fixed fraction
field. At each stage the construction stops at a regular ring and otherwise enlarges strictly. -/
def IsFiniteSemilocalDomainOverringSequence
    {R : Type u} [CommRing R] [IsDomain R]
    (S : ℕ → Subalgebra R (FractionRing R)) : Prop :=
  S 0 = ⊥ ∧
    ∀ n,
      IsNoetherianRing (S n) ∧
        IsDomain (S n) ∧
          Finite (MaximalSpectrum (S n)) ∧
            ringKrullDim (S n) = 1 ∧
              IsFractionRing (S n) (FractionRing R) ∧
                ∃ hle : S n ≤ S (n + 1),
                  (Subalgebra.inclusion hle).toRingHom.Finite ∧
                    ((IsRegularRing (S n) ∧ S (n + 1) = S n) ∨
                      (¬ IsRegularRing (S n) ∧ S n < S (n + 1)))

section General

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Finite (MaximalSpectrum R)]

/-- Remark 10.119.6 (1): if a maximal localization of a one-dimensional semilocal Noetherian
domain is not regular, then there is a strict finite overring in the same fraction field which is
again a one-dimensional semilocal Noetherian domain. -/
@[stacks 00PC]
theorem exists_strictFiniteOverring_of_nonregular_maximalLocalization
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    ∃ S : Subalgebra R (FractionRing R),
      ∃ hlt : (⊥ : Subalgebra R (FractionRing R)) < S,
        Module.Finite R S ∧
          IsNoetherianRing S ∧
            IsDomain S ∧
              Finite (MaximalSpectrum S) ∧
                ringKrullDim S = 1 ∧ IsFractionRing S (FractionRing R) := sorry

/-- Remark 10.119.6 (2): iterating the finite-overring construction gives a sequence in the
fixed fraction field whose first step is strict and which stabilizes exactly when a regular stage
is reached. -/
@[stacks 00PC]
theorem exists_finiteOverringSequence_of_nonregular_maximalLocalization
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    ∃ S : ℕ → Subalgebra R (FractionRing R),
      IsFiniteSemilocalDomainOverringSequence S ∧
        (⊥ : Subalgebra R (FractionRing R)) < S 1 := sorry

/-- Remark 10.119.6 (3): there is a characteristic-zero one-dimensional Noetherian local domain
with nonreduced completion for which the finite-overring sequence never stabilizes. -/
@[stacks 00PC]
theorem exists_charZero_nonstabilizing_finite_semilocal_domain_overring_sequence :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A)
      (_ : IsLocalRing A) (_ : CharZero A),
      ringKrullDim A = 1 ∧
        ¬ IsAnalyticallyUnramified A ∧
          ∃ S : ℕ → Subalgebra A (FractionRing A),
            IsFiniteSemilocalDomainOverringSequence S ∧ ∀ n, S n < S (n + 1) := sorry

end General

section PositiveCharacteristic

open scoped PthPowerSubfield

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]
  (f : PowerSeries k)

local notation "A" => finitePthPowerCoefficientSubring k p
local notation "R" => finitePthPowerCoefficientAdjoinSubring k p f

/-- Remark 10.119.6 (4): the positive-characteristic ring `R = A[f]` from Example 10.119.5,
with `f ∉ A`, admits a finite-overring sequence which never stabilizes. -/
@[stacks 00PC]
theorem positiveChar_exists_nonstabilizing_finiteOverringSequence
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (hf : f ∉ A) :
    ∃ S : ℕ → Subalgebra ↥R (FractionRing ↥R),
      IsFiniteSemilocalDomainOverringSequence S ∧ ∀ n, S n < S (n + 1) := sorry

end PositiveCharacteristic

section Stopping

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Finite (MaximalSpectrum R)]

/-- Remark 10.119.6 (5): if every maximal localization of the base ring is analytically
unramified, then every finite-overring sequence reaches a regular stage and is constant from that
stage onward. -/
@[stacks 00PC]
theorem exists_regularStage_of_analyticallyUnramified
    {S : ℕ → Subalgebra R (FractionRing R)}
    (hS : IsFiniteSemilocalDomainOverringSequence S)
    (hcompletion : ∀ m : MaximalSpectrum R,
      IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal)) :
    ∃ n : ℕ, IsRegularRing (S n) ∧ ∀ j, n ≤ j → S j = S n := sorry

end Stopping

#check @IsFiniteSemilocalDomainOverringSequence
#check @exists_strictFiniteOverring_of_nonregular_maximalLocalization
#check @exists_finiteOverringSequence_of_nonregular_maximalLocalization
#check @exists_charZero_nonstabilizing_finite_semilocal_domain_overring_sequence
#check @IsAnalyticallyUnramified.exists_charZero_localDomain_counterexample
#check @positiveChar_exists_nonstabilizing_finiteOverringSequence
#check @exists_regularStage_of_analyticallyUnramified

#print axioms IsFiniteSemilocalDomainOverringSequence
