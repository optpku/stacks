module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Pham–Brieskorn power-series hypersurfaces
-/

@[expose] public section

set_option backward.privateInPublic true

noncomputable section

open MvPowerSeries

namespace MvPowerSeries.PhamBrieskorn

/-- The Pham–Brieskorn power series `X 0 ^ r + X 1 ^ s + X 2 ^ t`. -/
def relation (r s t : ℕ) : MvPowerSeries (Fin 3) ℂ :=
  X 0 ^ r + X 1 ^ s + X 2 ^ t

/-- The Pham–Brieskorn power-series quotient by the principal relation. -/
abbrev Ring (r s t : ℕ) : Type :=
  MvPowerSeries (Fin 3) ℂ ⧸ Ideal.span {relation r s t}

/-- The class of the first coordinate in the Pham–Brieskorn quotient. -/
def x (r s t : ℕ) : Ring r s t :=
  Ideal.Quotient.mk _ (X 0)

/-- The class of the second coordinate in the Pham–Brieskorn quotient. -/
def y (r s t : ℕ) : Ring r s t :=
  Ideal.Quotient.mk _ (X 1)

/-- The class of the third coordinate in the Pham–Brieskorn quotient. -/
def z (r s t : ℕ) : Ring r s t :=
  Ideal.Quotient.mk _ (X 2)

/-- The defining coordinate relation in the Pham–Brieskorn quotient. -/
theorem x_pow_add_y_pow_add_z_pow (r s t : ℕ) :
    x r s t ^ r + y r s t ^ s + z r s t ^ t = 0 := sorry

/-- The binomial power series with rational exponent `1 / 7`. -/
def seventhRootSeries : PowerSeries ℂ :=
  PowerSeries.binomialSeries ℂ (7⁻¹ : ℚ)

set_option backward.privateInPublic true in
private theorem seventhRootSeries_pow :
    seventhRootSeries ^ 7 = 1 + PowerSeries.X := by
  have h : ∀ n : ℕ,
      seventhRootSeries ^ n = PowerSeries.binomialSeries ℂ (n * (7⁻¹ : ℚ)) := by
    intro n
    induction n with
    | zero => simp [seventhRootSeries]
    | succ n ih =>
        rw [pow_succ, ih, seventhRootSeries, ← PowerSeries.binomialSeries_add]
        congr 1
        push_cast
        ring
  have h7 : (7 : ℚ) * (7⁻¹ : ℚ) = 1 := by norm_num
  rw [h 7]
  norm_num
  simpa using (PowerSeries.binomialSeries_nat (A := ℂ) 1)

/-- The three power-series coordinates parametrizing the seven branches. -/
def psiCoords (ζ : rootsOfUnity 7 ℂ) : Fin 3 → PowerSeries ℂ :=
  ![PowerSeries.X ^ 7, PowerSeries.X ^ 3,
    -(PowerSeries.C ((ζ : ℂˣ) : ℂ) * PowerSeries.X ^ 2 * seventhRootSeries)]

set_option backward.privateInPublic true in
private theorem hasSubst_psiCoords (ζ : rootsOfUnity 7 ℂ) :
    HasSubst (psiCoords ζ) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i
  · change PowerSeries.constantCoeff (PowerSeries.X ^ 7) = 0
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow]
    norm_num
  · change PowerSeries.constantCoeff (PowerSeries.X ^ 3) = 0
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow]
    norm_num
  · change PowerSeries.constantCoeff
      (-(PowerSeries.C ((ζ : ℂˣ) : ℂ) * PowerSeries.X ^ 2 * seventhRootSeries)) = 0
    rw [map_neg, map_mul, map_mul, map_pow, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, zero_pow]
    all_goals simp

/-- The ambient substitution homomorphism determined by `psiCoords ζ`. -/
def psiCover (ζ : rootsOfUnity 7 ℂ) :
    MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] PowerSeries ℂ :=
  substAlgHom (hasSubst_psiCoords ζ)

set_option backward.privateInPublic true in
private theorem psiCover_map_relation (ζ : rootsOfUnity 7 ℂ) :
    psiCover ζ (relation 2 5 7) = 0 := by
  change substAlgHom (hasSubst_psiCoords ζ) (relation 2 5 7) = 0
  simp only [relation, map_add, map_pow]
  rw [substAlgHom_X (hasSubst_psiCoords ζ) 0,
    substAlgHom_X (hasSubst_psiCoords ζ) 1,
    substAlgHom_X (hasSubst_psiCoords ζ) 2]
  change (PowerSeries.X ^ 7) ^ 2 + (PowerSeries.X ^ 3) ^ 5 +
      (-(PowerSeries.C ((ζ : ℂˣ) : ℂ) * PowerSeries.X ^ 2 * seventhRootSeries)) ^ 7 = 0
  have hbranch :
      (-(PowerSeries.C ((ζ : ℂˣ) : ℂ) * PowerSeries.X ^ 2 * seventhRootSeries)) ^ 7 =
        -(PowerSeries.C ((ζ : ℂˣ) : ℂ) ^ 7) * (PowerSeries.X ^ 2) ^ 7 *
          seventhRootSeries ^ 7 := by
    rw [neg_pow, mul_pow, mul_pow]
    ring_nf
  rw [hbranch, seventhRootSeries_pow]
  have hζ : ((ζ : ℂˣ) : ℂ) ^ 7 = 1 := by
    have h := ζ.2
    change (ζ : ℂˣ) ^ 7 = 1 at h
    exact congrArg (fun u : ℂˣ => (u : ℂ)) h
  have hC : (PowerSeries.C ((ζ : ℂˣ) : ℂ)) ^ 7 = 1 := by
    rw [← (PowerSeries.C : ℂ →+* PowerSeries ℂ).map_pow, hζ]
    exact map_one _
  rw [hC]
  ring

set_option backward.privateInPublic true in
private theorem psiCover_mem_ideal (ζ : rootsOfUnity 7 ℂ) {f : MvPowerSeries (Fin 3) ℂ}
    (hf : f ∈ Ideal.span {relation 2 5 7}) : psiCover ζ f = 0 := by
  have hle : Ideal.span {relation 2 5 7} ≤ RingHom.ker (psiCover ζ).toRingHom := by
    refine Ideal.span_le.2 ?_
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact psiCover_map_relation ζ
  exact hle hf

/-- The branch homomorphism from the `(2, 5, 7)` quotient to power series. -/
def psi (ζ : rootsOfUnity 7 ℂ) : Ring 2 5 7 →+* PowerSeries ℂ :=
  Ideal.Quotient.lift (Ideal.span {relation 2 5 7}) (psiCover ζ).toRingHom
    fun _ hf ↦ psiCover_mem_ideal ζ hf

/-- The first coordinate is sent to `T ^ 7` by `psi ζ`. -/
theorem psi_x (ζ : rootsOfUnity 7 ℂ) :
    psi ζ (x 2 5 7) = PowerSeries.X ^ 7 := sorry

/-- The second coordinate is sent to `T ^ 3` by `psi ζ`. -/
theorem psi_y (ζ : rootsOfUnity 7 ℂ) :
    psi ζ (y 2 5 7) = PowerSeries.X ^ 3 := sorry

/-- The third coordinate is sent to its binomial-series branch value by `psi ζ`. -/
theorem psi_z (ζ : rootsOfUnity 7 ℂ) :
    psi ζ (z 2 5 7) =
      -(PowerSeries.C ((ζ : ℂˣ) : ℂ) * PowerSeries.X ^ 2 * seventhRootSeries) := sorry

/-- The kernel ideal defining the branch indexed by `ζ`. -/
def prime (ζ : rootsOfUnity 7 ℂ) : Ideal (Ring 2 5 7) :=
  RingHom.ker (psi ζ)

/-- Each branch kernel is prime because its target power-series ring is a domain. -/
instance prime_isPrime (ζ : rootsOfUnity 7 ℂ) : (prime ζ).IsPrime := by
  exact RingHom.ker_isPrime (psi ζ)

/-- Each branch kernel has height one. -/
theorem prime_height (ζ : rootsOfUnity 7 ℂ) : (prime ζ).height = 1 := sorry

/-- The element `x ^ 3 - y ^ 7` in the `(2, 5, 7)` quotient. -/
def xyDiff : Ring 2 5 7 :=
  x 2 5 7 ^ 3 - y 2 5 7 ^ 7

/-- The zero locus of `xyDiff` is the union of the seven branch zero loci. -/
theorem zeroLocus_xyDiff_eq_iUnion_prime :
    PrimeSpectrum.zeroLocus {xyDiff} =
      ⋃ ζ : rootsOfUnity 7 ℂ, PrimeSpectrum.zeroLocus (prime ζ) := sorry

/-- The quotient by `xyDiff` is local. -/
instance instIsLocalRing_xyDiffQuotient :
    IsLocalRing (Ring 2 5 7 ⧸ Ideal.span {xyDiff}) := sorry

/-- The quotient by `xyDiff` is reduced away from its closed point. -/
theorem xyDiff_isReduced_away_from_closedPoint
    (p : PrimeSpectrum (Ring 2 5 7 ⧸ Ideal.span {xyDiff}))
    (hp : p ≠ IsLocalRing.closedPoint (Ring 2 5 7 ⧸ Ideal.span {xyDiff})) :
    IsReduced (Localization.AtPrime p.asIdeal) := sorry

/-- If `1 < r < s < t` are pairwise coprime and `(r, s, t) ≠ (2, 3, 5)`,
then the corresponding Pham–Brieskorn quotient is not factorial. -/
theorem not_uniqueFactorizationMonoid {r s t : ℕ} (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (h_rs : Nat.Coprime r s) (h_rt : Nat.Coprime r t) (h_st : Nat.Coprime s t)
    (h235 : ¬ (r = 2 ∧ s = 3 ∧ t = 5)) :
    ¬ UniqueFactorizationMonoid (Ring r s t) := sorry

/-- The `(2, 5, 7)` Pham–Brieskorn quotient is not factorial. -/
theorem not_uniqueFactorizationMonoid_two_five_seven :
    ¬ UniqueFactorizationMonoid (Ring 2 5 7) := sorry

end MvPowerSeries.PhamBrieskorn
