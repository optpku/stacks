/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Frobenius.Polynomial
public import ReasLib.FieldTheory.Polynomial.SeparableDegree

@[expose] public section

open Polynomial

universe u v

namespace FieldExtension

section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

namespace Frobenius

/-- If a root in a field extension of a characteristic-`p` field satisfies a separable polynomial
in the Frobenius image on coefficients, then it is itself in the Frobenius image. -/
theorem memPowRangeOfIsRoot
    {α : L} {P : K[X]} (hPsep : P.Separable) (hPα : aeval α P = 0)
    (hP : P ∈ Polynomial.Frobenius.range K p) :
    α ∈ Set.range (fun β : L ↦ β ^ p) := by
  obtain ⟨Q, hmap⟩ := hP
  have hmap' : Q.map (frobenius K p) = P := by
    simpa only [Polynomial.coe_mapRingHom] using hmap
  have hQsep : Q.Separable :=
    (Polynomial.separable_map (frobenius K p)).1 (hmap' ▸ hPsep)
  by_contra hα
  -- Local instance justification (proof-local temporary data): transport the base characteristic along the injective field map for the irreducibility argument.
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let g : L[X] := X ^ p - C α
  have hgirr : Irreducible g := by
    refine X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) ?_
    simpa [Set.mem_range, frobenius_def, g] using hα
  -- Local instance justification (proof-local temporary data): provide the field structure on the root-adjunction used in this irreducibility argument.
  letI : Fact (Irreducible g) := ⟨hgirr⟩
  let M := AdjoinRoot g
  -- Local instance justification (proof-local temporary data): realize the temporary tower `K → L → M` needed to transport the polynomial root equation.
  letI : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  -- Local instance justification (proof-local temporary data): transfer exponent characteristic to the temporary irreducible root extension.
  haveI : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
  let β : M := AdjoinRoot.root g
  have hβg_eval : g.eval₂ (AdjoinRoot.of g) β = 0 := by
    dsimp [β]
    exact AdjoinRoot.eval₂_root g
  have hβg : aeval β g = 0 := by
    simpa [Polynomial.aeval_def, M] using hβg_eval
  have hβpow : β ^ p = algebraMap L M α := by
    simpa [g, M, β] using root_X_pow_sub_C_pow p α
  have hPαM : aeval (algebraMap L M α) P = 0 := by
    have hcomp :
        (algebraMap K M).comp (RingHom.id K) = (algebraMap L M).comp (algebraMap K L) := by
      ext x
      rfl
    have hmapP : algebraMap L M (aeval α P) = aeval (algebraMap L M α) P := by
      simpa using P.map_aeval_eq_aeval_map hcomp α
    rw [← hmapP]
    simpa using congrArg (algebraMap L M) hPα
  have hβQfrobenius : frobenius M p (aeval β Q) = 0 := by
    have hcomp :
        (algebraMap K M).comp (frobenius K p) = (frobenius M p).comp (algebraMap K M) := by
      ext x
      simp [frobenius_def]
    calc
      frobenius M p (aeval β Q) = aeval (frobenius M p β) (Q.map (frobenius K p)) := by
        simpa [M] using Q.map_aeval_eq_aeval_map hcomp β
      _ = aeval (algebraMap L M α) P := by simp [frobenius_def, hβpow, hmap']
      _ = 0 := hPαM
  have hβQ : aeval β Q = 0 := by
    exact (pow_eq_zero_iff (Nat.Prime.ne_zero (Fact.out : p.Prime))).1 <|
      by simpa [frobenius_def] using hβQfrobenius
  have hβQ' : aeval β (Q.map (algebraMap K L)) = 0 := by
    have hcomp : (algebraMap L M).comp (algebraMap K L) = algebraMap K M := by
      ext x
      rfl
    rw [← Q.aeval_eq_aeval_map hcomp β]
    exact hβQ
  have hgdvd : g ∣ Q.map (algebraMap K L) := by
    rw [minpoly.eq_of_irreducible_of_monic hgirr hβg
      (monic_X_pow_sub_C α (Nat.Prime.ne_zero (Fact.out : p.Prime)))]
    exact minpoly.dvd L β hβQ'
  have hgsep : g.Separable := by
    exact Polynomial.Separable.of_dvd ((Polynomial.separable_map (algebraMap K L)).2 hQsep) hgdvd
  exact ((Polynomial.separable_iff_derivative_ne_zero hgirr).1 hgsep) <| by
    simp [g, Polynomial.derivative_pow]

/-- A root satisfying the Frobenius-image hypothesis of the preceding theorem has a `p`th root in
the ambient field. -/
theorem existsPthRootOfIsRoot
    {α : L} {P : K[X]} (hPsep : P.Separable) (hPα : aeval α P = 0)
    (hP : P ∈ Polynomial.Frobenius.range K p) :
    ∃ β : L, β ^ p = α := by
  simpa [Set.mem_range] using
    memPowRangeOfIsRoot hPsep hPα hP

/-- A `p`th root of a separable Frobenius-image polynomial root remains in an intermediate field
whenever its `p`th power belongs to that intermediate field. -/
theorem memIntermediateFieldOfPowEqOfIsRoot
    {F : Type*} {A : Type*}
    [Field F] [Field A] [Algebra F A]
    (L : IntermediateField F A)
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {α β : A} {P : Polynomial F}
    (hβ : β ^ p = α)
    (hαL : α ∈ L)
    (hPsep : P.Separable)
    (hPα : Polynomial.aeval α P = 0)
    (hmap : P ∈ Polynomial.Frobenius.range F p) :
    β ∈ L := by
  -- Local instance justification (proof-local temporary data): transfer characteristic `p` to the ambient field so the Frobenius map is injective when comparing the two roots.
  letI : CharP A p := charP_of_injective_algebraMap (algebraMap F A).injective p
  let αL : L := ⟨α, hαL⟩
  have hPαL : Polynomial.aeval αL P = 0 := by
    apply (algebraMap L A).injective
    have h_eval :
        (algebraMap L A) ((Polynomial.aeval αL) P) = Polynomial.aeval α P := by
      simpa [αL] using
        (Polynomial.aeval_algHom_apply (L.val.restrictScalars F) αL P).symm
    exact h_eval.trans hPα
  obtain ⟨γ, hγ⟩ :=
    existsPthRootOfIsRoot
      (K := F) (L := L) hPsep hPαL hmap
  have hγA : (γ : A) ^ p = α := by
    simpa [αL] using congrArg (fun z : L ↦ (z : A)) hγ
  have hβ_eq : β = γ := by
    exact (frobenius A p).injective (by simp [frobenius_def, hβ, hγA])
  simp [hβ_eq, γ.2]

end Frobenius

namespace SeparableRoot

/-- Lemma 9.28.2 (Tag 031V): if a root of a separable polynomial over a characteristic-`p` field
has coefficientwise `p`th-power coefficients, then the root is a `p`th power in the extension. -/
theorem existsPthRootOfCoefficientsArePthPowers
    {α : L} {P : K[X]} (hPsep : P.Separable) (hPα : aeval α P = 0)
    (hcoeff : ∀ n : ℕ, ∃ b : K, P.coeff n = b ^ p) :
    ∃ β : L, β ^ p = α := by
  have hmap : P ∈ Polynomial.Frobenius.range K p :=
    (Polynomial.Frobenius.mem_range_iff_coeff_eq_pow).2 hcoeff
  exact Frobenius.existsPthRootOfIsRoot hPsep hPα hmap

/-- If every coefficient of the minimal polynomial of a separable element is a `p`th power, then
the element itself is a `p`th power. -/
theorem existsPthRootOfMinpolyCoefficientsArePthPowers {α : L} (hα : IsSeparable K α)
    (hcoeff : ∀ n : ℕ, ∃ b : K, (minpoly K α).coeff n = b ^ p) :
    ∃ β : L, β ^ p = α := by
  exact existsPthRootOfCoefficientsArePthPowers hα (minpoly.aeval K α)
    hcoeff

end SeparableRoot

end

end FieldExtension
