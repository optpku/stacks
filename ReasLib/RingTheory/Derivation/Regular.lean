/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Tactic.CrossRefAttribute
import Mathlib.RingTheory.Filtration

/-!
# Regular Elements Detected by Derivations

An `R`-derivation that sends an element to one detects both its
non-nilpotence and, in the Noetherian local rational setting, regularity.
-/

@[expose] public section

namespace Derivation

universe u v

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Algebra ℚ S]

/-- Lemma 10.140.6, tag `00TW`: an element on which a derivation takes the value one is not
nilpotent over a rational algebra. -/
@[stacks 00TW "derivation detects non-nilpotence"]
theorem not_isNilpotent_of_apply_eq_one
    [Nontrivial S] (delta : Derivation R S S) (f : S) (hdelta : delta f = 1) :
    ¬ IsNilpotent f := by
  intro hf
  obtain ⟨n, hn⟩ := hf
  induction n with
  | zero => exact one_ne_zero (by simpa only [pow_zero] using hn)
  | succ n ih =>
      apply ih
      have hd := congrArg delta hn
      rw [delta.leibniz_pow, delta.map_zero, hdelta] at hd
      simp only [Nat.add_sub_cancel, smul_eq_mul, mul_one, nsmul_eq_mul] at hd
      have huQ : IsUnit (n + 1 : ℚ) := by
        rw [isUnit_iff_ne_zero]
        exact_mod_cast Nat.succ_ne_zero n
      have huS : IsUnit (n + 1 : S) := by
        simpa using huQ.map (algebraMap ℚ S)
      exact huS.mul_left_cancel (by simpa using hd)

/-- Lemma 10.140.6, tag `00TW`: in a Noetherian local rational algebra, an element on which a
derivation takes the value one is regular. -/
@[stacks 00TW "derivation detects regular elements"]
theorem isRegular_of_apply_eq_one
    [IsLocalRing S] [IsNoetherianRing S]
    (delta : Derivation R S S) (f : S) (hdelta : delta f = 1) :
    IsRegular f := by
  rw [isRegular_iff_eq_zero_of_mul]
  suffices hcancel : ∀ a : S, f * a = 0 → a = 0 by
    exact ⟨hcancel, fun a ha ↦ hcancel a (by simpa [mul_comm] using ha)⟩
  intro a hfa
  by_cases hf : IsUnit f
  · exact hf.mul_left_cancel (by simpa using hfa)
  have ha_pow : ∀ n : ℕ, a ∈ (Ideal.span {f}) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ih
        obtain ⟨b, hb⟩ := ih
        have hfb : f ^ (n + 1) * b = 0 := by
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc, hb] using hfa
        have hd := congrArg delta hfb
        rw [delta.leibniz, delta.leibniz_pow, delta.map_zero, hdelta] at hd
        simp only [Nat.add_sub_cancel, smul_eq_mul, mul_one, nsmul_eq_mul] at hd
        have hba : b * (((n + 1 : ℕ) : S) * f ^ n) = ((n + 1 : ℕ) : S) * a := by
          rw [mul_comm (((n + 1 : ℕ) : S)), ← mul_assoc, hb, mul_comm]
        rw [hba] at hd
        have huQ : IsUnit (n + 1 : ℚ) := by
          rw [isUnit_iff_ne_zero]
          exact_mod_cast Nat.succ_ne_zero n
        have huS : IsUnit (n + 1 : S) := by
          simpa using huQ.map (algebraMap ℚ S)
        apply ((Ideal.span {f}) ^ (n + 1)).unit_mul_mem_iff_mem huS |>.mp
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
        refine ⟨-delta b, ?_⟩
        rw [neg_mul, mul_comm (delta b)]
        exact neg_eq_of_add_eq_zero_left (by simpa [add_comm] using hd)
  have ha_inf : a ∈ ⨅ n : ℕ, (Ideal.span {f}) ^ n := Ideal.mem_iInf.mpr ha_pow
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {f})
    (Ideal.span_singleton_eq_top.not.mpr hf)] at ha_inf
  simpa using ha_inf

end Derivation
