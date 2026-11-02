/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.KrullDimension.Module
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Polynomial
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Multiplicity
public import ReasLib.RingTheory.Module.Support.Annihilator
public import ReasLib.RingTheory.Module.Support.FiniteLength
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.TFAE

@[expose] public section

universe u v

open scoped Pointwise

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- For a finite module over a Noetherian local ring, finite colength of `I` on `M`
is equivalent to the corresponding condition after adjoining the annihilator, passing to
the quotient by the annihilator, restricting support to the closed point, bounding support
dimension by zero, or requiring finite module length. -/
theorem finiteColength_tfae [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (hproper : I + Module.annihilator R M ≠ ⊤) :
    List.TFAE
      [ (I + Module.annihilator R M).IsIdealOfDefinition
      , (I.map (Ideal.Quotient.mk (Module.annihilator R M))).radical =
          (IsLocalRing.maximalIdeal R).map
            (Ideal.Quotient.mk (Module.annihilator R M))
      , Module.support R (M ⧸ (I • ⊤ : Submodule R M)) ⊆
          {IsLocalRing.closedPoint R}
      , Module.supportDim R (M ⧸ (I • ⊤ : Submodule R M)) ≤ 0
      , Module.length R (M ⧸ (I • ⊤ : Submodule R M)) < ⊤
      ] := by
  let J := I + Module.annihilator R M
  let Q := M ⧸ (I • ⊤ : Submodule R M)
  let f := Ideal.Quotient.mk (Module.annihilator R M)
  have hJ : J ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hproper
  have hann : Module.annihilator R M ≤ IsLocalRing.maximalIdeal R :=
    (le_sup_right : Module.annihilator R M ≤ I ⊔ Module.annihilator R M).trans hJ
  have hmap : (I.map f).comap f = J := by
    dsimp [f, J]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hmax : ((IsLocalRing.maximalIdeal R).map f).comap f =
      IsLocalRing.maximalIdeal R := by
    exact Ideal.comap_map_mk hann
  have hs : Module.support R Q = PrimeSpectrum.zeroLocus J := by
    dsimp [Q, J]
    rw [Module.support_quotient, Module.support_eq_zeroLocus,
      PrimeSpectrum.zeroLocus_sup, Set.inter_comm]
  tfae_have 1 ↔ 2 := by
    change J.radical = IsLocalRing.maximalIdeal R ↔
      (I.map f).radical = (IsLocalRing.maximalIdeal R).map f
    rw [← (Ideal.comap_injective_of_surjective f Ideal.Quotient.mk_surjective).eq_iff,
      Ideal.comap_radical, hmap, hmax]
  tfae_have 1 ↔ 3 := by
    change J.radical = IsLocalRing.maximalIdeal R ↔
      Module.support R Q ⊆ {IsLocalRing.closedPoint R}
    rw [hs, IsLocalRing.closedPoint,
      ← PrimeSpectrum.zeroLocus_eq_singleton (IsLocalRing.maximalIdeal R),
      PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
    exact ⟨fun h ↦ h.ge, fun h ↦
      (IsLocalRing.le_maximalIdeal (fun e ↦ hproper (Ideal.radical_eq_top.mp e))).antisymm h⟩
  tfae_have 3 → 4 := by
    intro h
    haveI : Subsingleton (Module.support R Q) := ⟨fun x y ↦ Subtype.ext
      ((Set.mem_singleton_iff.mp (h x.2)).trans (Set.mem_singleton_iff.mp (h y.2)).symm)⟩
    exact Order.krullDim_nonpos_of_subsingleton
  tfae_have 4 → 5 := by
    intro hdim
    let A := R ⧸ Module.annihilator R Q
    letI : Module A Q := Module.quotientAnnihilator
    letI : IsScalarTower R A Q :=
      Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R Q)
    haveI : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr (by
      change ringKrullDim (R ⧸ Module.annihilator R Q) ≤ (0 : WithBot ℕ∞)
      rw [← Module.supportDim_eq_ringKrullDim_quotient_annihilator R Q]
      exact hdim)
    haveI : IsArtinianRing A := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    haveI : Module.Finite A Q := Module.Finite.of_restrictScalars_finite R A Q
    haveI : IsArtinian R Q :=
      isArtinian_of_surjective_algebraMap (R := A) Ideal.Quotient.mk_surjective
    exact Module.length_ne_top.lt_top
  tfae_have 5 → 3 := by
    intro hlen p hp
    haveI : IsArtinian R Q :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (Module.length_ne_top_iff.mp hlen.ne)).2
    obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hp
    let g := LinearMap.toSpanSingleton R Q m
    have hg : LinearMap.ker g ≤ p.asIdeal := by
      simpa only [Submodule.annihilator_span_singleton] using hm
    haveI : IsArtinian R (R ⧸ LinearMap.ker g) :=
      (LinearMap.quotKerEquivRange g).isArtinian_iff.mpr inferInstance
    haveI : IsArtinianRing (R ⧸ LinearMap.ker g) := isArtinian_of_tower R inferInstance
    let q := p.asIdeal.map (Ideal.Quotient.mk (LinearMap.ker g))
    haveI : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using hg)
    haveI : q.IsMaximal := IsArtinianRing.isMaximal_of_isPrime q
    have hpm : p.asIdeal.IsMaximal := by
      have h := Ideal.comap_isMaximal_of_surjective
        (Ideal.Quotient.mk (LinearMap.ker g)) Ideal.Quotient.mk_surjective (K := q)
      simpa only [q, Ideal.comap_map_mk hg] using h
    exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hpm))
  tfae_finish

/-- Adjoining the annihilator of `M` to `I` does not change the submodule killed by any power
of the ideal. -/
theorem pow_smul_top_add_annihilator (I : Ideal R) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) =
      ((I + Module.annihilator R M) ^ n • ⊤ : Submodule R M) := by
  have hann (N : Submodule R M) : Module.annihilator R M • N = ⊥ := by
    apply le_antisymm ?_ bot_le
    calc
      Module.annihilator R M • N ≤ Module.annihilator R M • ⊤ :=
        smul_mono_right _ le_top
      _ = ⊥ := by rw [← Submodule.annihilator_top, Submodule.annihilator_smul]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Submodule.mul_smul, Submodule.mul_smul, ← ih,
      Ideal.add_eq_sup, Submodule.sup_smul, hann, sup_bot_eq]

/-- Powers of the image of `I` in `R ⧸ Module.annihilator R M`, restricted back to `R`, give
the same submodules of `M` as powers of `I`. -/
theorem pow_smul_top_quotientAnnihilator (I : Ideal R) (n : ℕ) :
    let A := R ⧸ Module.annihilator R M
    -- Local instance justification (search instability): the canonical quotient-annihilator action is intentionally selected locally.
    letI : Module A M := Module.quotientAnnihilator
    -- Local instance justification (search instability): the scalar tower is tied to the selected quotient-annihilator action.
    letI : IsScalarTower R A M :=
      Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
    Submodule.restrictScalars R
        ((I.map (Ideal.Quotient.mk (Module.annihilator R M))) ^ n • ⊤ :
          Submodule A M) =
      (I ^ n • ⊤ : Submodule R M) := by
  dsimp only
  let A := R ⧸ Module.annihilator R M
  letI : Module A M := Module.quotientAnnihilator
  letI : IsScalarTower R A M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  rw [← Ideal.map_pow]
  exact Ideal.smul_restrictScalars (I ^ n) (⊤ : Submodule A M)

/-- The Hilbert--Samuel `χ`-function is unchanged after adjoining the annihilator of the
module to the ideal. -/
theorem chi_add_annihilator (I : Ideal R) (n : ℕ) :
    I.hilbertSamuelChi M n =
      (I + Module.annihilator R M).hilbertSamuelChi M n := by
  unfold Ideal.hilbertSamuelChi
  rw [pow_smul_top_add_annihilator]

/-- The Hilbert--Samuel `χ`-function agrees with that of the image ideal over the canonical
annihilator quotient of the scalar ring. -/
theorem chi_quotientAnnihilator (I : Ideal R) (n : ℕ) :
    let A := R ⧸ Module.annihilator R M
    -- Local instance justification (search instability): the canonical quotient-annihilator action is intentionally selected locally.
    letI : Module A M := Module.quotientAnnihilator
    I.hilbertSamuelChi M n =
      (I.map (Ideal.Quotient.mk (Module.annihilator R M))).hilbertSamuelChi M n := by
  dsimp only
  let A := R ⧸ Module.annihilator R M
  letI : Module A M := Module.quotientAnnihilator
  letI : IsScalarTower R A M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  let N : Submodule A M :=
    (I.map (Ideal.Quotient.mk (Module.annihilator R M))) ^ (n + 1) • ⊤
  change Module.length R (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) =
    Module.length A (M ⧸ N)
  calc
    _ = Module.length R (M ⧸ N.restrictScalars R) :=
      (Submodule.quotEquivOfEq _ _
        (pow_smul_top_quotientAnnihilator I (n + 1)).symm).length_eq
    _ = Module.length R (M ⧸ N) :=
      (Submodule.Quotient.restrictScalarsEquiv R N).length_eq
    _ = Module.length A (M ⧸ N) :=
      Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective)

/-- If adjoining the annihilator makes `I` an ideal of definition, the canonical Hilbert--Samuel
polynomial for `I` represents its `χ`-function eventually. -/
theorem chiPolynomial_spec_of_add_annihilator [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R M] (I : Ideal R)
    (hI : (I + Module.annihilator R M).IsIdealOfDefinition) :
    (chiPolynomial I M).EventuallyEqNat
      (fun n ↦ ((I.hilbertSamuelChi M n).toNat : ℚ)) := by
  have hfun : (fun n ↦ ((I.hilbertSamuelChi M n).toNat : ℚ)) =
      (fun n ↦ (((I + Module.annihilator R M).hilbertSamuelChi M n).toNat : ℚ)) := by
    funext n
    rw [chi_add_annihilator]
  simpa only [chiPolynomial, hfun] using
    chiPolynomial_spec_of_isIdealOfDefinition (I + Module.annihilator R M) M hI

/-- Degree-`d` Hilbert--Samuel multiplicity is unchanged when the annihilator of the module is
adjoined to the ideal under the finite-colength hypothesis. -/
theorem multiplicityInDegree_add_annihilator [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R M] (I : Ideal R) (d : ℕ)
    (hI : (I + Module.annihilator R M).IsIdealOfDefinition) :
    multiplicityInDegree I M d =
      multiplicityInDegree (I + Module.annihilator R M) M d := by
  have hchi : chiPolynomial I M = chiPolynomial (I + Module.annihilator R M) M := by
    unfold chiPolynomial
    congr 1
    funext n
    rw [chi_add_annihilator]
  unfold multiplicityInDegree
  rw [hchi]

end Ideal.HilbertSamuel
