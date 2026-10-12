/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Depth.Equiv

@[expose] public section

/-!
# Serre Conditions

@stack 031P

Serre's conditions (R_k) and (S_k) characterize regularity and depth properties of Noetherian
rings and modules.

## Main definitions

* `Module.SerreConditionS` — module-level Serre condition (S_k).
* `SerreConditionR` — ring regularity in codimension ≤ k.
* `SerreConditionS` — ring depth condition (S_k) (specialized from the module version).

## Main results

* `Module.serreConditionS_iff` — the defining finite-module and local-depth conditions.
* `LinearEquiv.serreConditionS_iff` — `(S_k)` is invariant under linear equivalence.
* `Module.SerreConditionS.of_le` — module `(S_k)` is monotone in `k`.
* `SerreConditionR.of_le` and `SerreConditionS.of_le` — ring conditions are monotone in `k`.
* `SerreConditionS.moduleDepth_localizationAtPrime_ge_min` — ring depth bound from self-module.
-/

universe u v

open scoped ENat

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-- A finite `R`-module satisfies Serre's condition `(S_k)` if, for every prime `𝔭`, the depth
of `M_𝔭` is at least `min(k, dim(Supp(M_𝔭)))`. -/
@[stacks 031P]
class SerreConditionS (k : ℕ) : Prop extends Module.Finite R M where
  moduleDepth_localizationAtPrime_ge_min_supportDim :
    ∀ p : PrimeSpectrum R,
      WithBot.some
          (moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) :
            ℕ∞) ≥
        min (k : WithBot ℕ∞)
          (_root_.Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M))

namespace SerreConditionS

/-- A module satisfying `(S_k)` also satisfies `(S_l)` for every `l ≤ k`. -/
theorem of_le {k l : ℕ} (h : Module.SerreConditionS R M k) (hlk : l ≤ k) :
    Module.SerreConditionS R M l := sorry

/-- Serre's condition `(S_k)` is invariant under linear equivalence. -/
theorem of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] {k : ℕ}
    (e : M ≃ₗ[R] N) [hM : Module.SerreConditionS R M k] :
    Module.SerreConditionS R N k := sorry

end SerreConditionS

/-- For a finite module, the Serre condition is exactly its primewise local-depth bound. -/
theorem serreConditionS_iff [Module.Finite R M] {k : ℕ} :
    SerreConditionS R M k ↔
      ∀ p : PrimeSpectrum R,
        WithBot.some
            (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (_root_.Module.supportDim (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M)) := sorry

end Module

namespace LinearEquiv

/-- Linearly equivalent modules satisfy the same Serre condition `(S_k)`. -/
theorem serreConditionS_iff {N : Type*} [AddCommGroup N] [Module R N] {k : ℕ}
    (e : M ≃ₗ[R] N) :
    Module.SerreConditionS R M k ↔ Module.SerreConditionS R N k := sorry

end LinearEquiv

/-- A Noetherian ring satisfies Serre's condition `(R_k)` if every localization at a prime of
height at most `k` is a regular local ring. -/
@[stacks 031P]
class SerreConditionR (k : ℕ) : Prop extends IsNoetherianRing R where
  isRegularLocalRing_localizationAtPrime :
    ∀ p : PrimeSpectrum R,
      Ideal.height p.asIdeal ≤ k →
        IsRegularLocalRing (Localization.AtPrime p.asIdeal)

/-- A Noetherian ring satisfies Serre's condition `(S_k)` if, for every prime `𝔭`, the depth
of `R_𝔭` is at least `min(k, dim(R_𝔭))`. -/
@[stacks 031P]
class SerreConditionS (k : ℕ) : Prop extends IsNoetherianRing R, Module.SerreConditionS R R k

/-- The ring Serre condition `(R_k)` is exactly Noetherianity together with regularity of all
prime localizations of height at most `k`. -/
theorem serreConditionR_iff {k : ℕ} :
    SerreConditionR R k ↔
      IsNoetherianRing R ∧
        ∀ p : PrimeSpectrum R,
          Ideal.height p.asIdeal ≤ k → IsRegularLocalRing (Localization.AtPrime p.asIdeal) := sorry

/-- The ring Serre condition `(S_k)` is the self-module condition together with Noetherianity. -/
theorem serreConditionS_iff {k : ℕ} :
    SerreConditionS R k ↔ IsNoetherianRing R ∧ Module.SerreConditionS R R k := sorry

namespace SerreConditionR

/-- A ring satisfying `(R_k)` also satisfies `(R_l)` for every `l ≤ k`. -/
theorem of_le {k l : ℕ} (h : SerreConditionR R k) (hlk : l ≤ k) :
    SerreConditionR R l := sorry

end SerreConditionR

namespace SerreConditionS

/-- A ring satisfying `(S_k)` also satisfies `(S_l)` for every `l ≤ k`. -/
theorem of_le {k l : ℕ} (h : SerreConditionS R k) (hlk : l ≤ k) :
    SerreConditionS R l := sorry

/-- The ring-theoretic depth bound recovered from the self-module owner. -/
theorem moduleDepth_localizationAtPrime_ge_min {k : ℕ} (h : SerreConditionS R k)
    (p : PrimeSpectrum R) :
    WithBot.some
        (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) : ℕ∞) ≥
      min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p.asIdeal)) := by
  rw [← _root_.Module.supportDim_self_eq_ringKrullDim]
  simpa using h.toSerreConditionS.moduleDepth_localizationAtPrime_ge_min_supportDim p

end SerreConditionS

end

/- The low-degree Serre conditions used throughout commutative algebra. -/
notation:max R:max " ⊧ " "(" "R₁" ")" => SerreConditionR R 1
notation:max R:max " ⊧ " "(" "S₂" ")" => SerreConditionS R 2
