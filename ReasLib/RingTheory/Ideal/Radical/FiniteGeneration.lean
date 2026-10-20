/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Oka
import Mathlib.RingTheory.Finiteness.Ideal
import ReasLib.RingTheory.Ideal.Colon
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite generation up to radical

@stack 0G2Z
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- An ideal is finitely generated up to radical if its radical is the radical of a finitely
generated ideal. -/
@[stacks 0G2Z "finite generation up to radical"]
def FGUpToRadical (I : Ideal R) : Prop :=
  ∃ J : Ideal R, J.FG ∧ I.radical = J.radical

namespace FG

/-- A finitely generated ideal is finitely generated up to radical. -/
@[stacks 0G2Z "finitely generated ideals are finitely generated up to radical"]
theorem fgUpToRadical {I : Ideal R} (hI : I.FG) : I.FGUpToRadical :=
  ⟨I, hI, rfl⟩

end FG

/-- Finite generation up to radical depends only on the radical. -/
theorem fgUpToRadical_congr {I J : Ideal R} (h : I.radical = J.radical) :
    I.FGUpToRadical ↔ J.FGUpToRadical := by
  constructor
  · rintro ⟨K, hKfg, hIK⟩
    exact ⟨K, hKfg, h.symm.trans hIK⟩
  · rintro ⟨K, hKfg, hJK⟩
    exact ⟨K, hKfg, h.trans hJK⟩

/-- Passing to the radical does not change finite generation up to radical. -/
@[simp, stacks 0G2Z "finite generation up to radical is radical-invariant"]
theorem radical_fgUpToRadical (I : Ideal R) :
    I.radical.FGUpToRadical ↔ I.FGUpToRadical :=
  fgUpToRadical_congr (radical_idem I)

namespace IsRadical

/-- For a radical ideal, finite generation up to radical means being the radical of a finitely
generated ideal. -/
@[stacks 0G2Z "radical ideals finitely generated up to radical"]
theorem fgUpToRadical_iff {I : Ideal R} (hI : I.IsRadical) :
    I.FGUpToRadical ↔ ∃ J : Ideal R, J.FG ∧ I = J.radical := by
  simp [FGUpToRadical, hI.radical]

end IsRadical

/-- A finitely generated-up-to-radical ideal contains a finitely generated ideal with the same
radical. -/
@[stacks 0G2Z "finitely generated witness inside an ideal"]
theorem FGUpToRadical.exists_fg_le {I : Ideal R} (hI : I.FGUpToRadical) :
    ∃ J : Ideal R, J.FG ∧ J ≤ I ∧ I.radical = J.radical := by
  rcases hI with ⟨J, hJfg, hrad⟩
  have hJle : J ≤ I.radical := by
    rw [hrad]
    exact le_radical
  obtain ⟨n, hn⟩ := exists_pow_le_of_le_radical_of_fg hJle hJfg
  refine ⟨J ^ (n + 1), hJfg.pow,
    (pow_le_pow_right (Nat.le_succ n)).trans hn, ?_⟩
  exact hrad.trans (radical_pow (I := J) (Nat.succ_ne_zero n)).symm

/-- The Oka identity `√((I + J) * (I : J)) = √I`. -/
@[stacks 0G2Z "Oka radical identity"]
theorem radical_sup_mul_colon (I J : Ideal R) :
    ((I ⊔ J) * I.colon J).radical = I.radical := by
  apply le_antisymm
  · exact radical_mono (by
      rw [sup_mul]
      exact sup_le mul_le_right (mul_colon_le I J))
  · refine (radical_le_radical_iff).2 ?_
    intro x hx
    have hx_colon : x ∈ I.colon J := by
      rw [Submodule.mem_colon]
      intro j hj
      exact I.mul_mem_right j hx
    exact ⟨2, by simpa [pow_two] using mul_mem_mul (mem_sup_left hx) hx_colon⟩

/-- If the supremum of a nonempty chain is finitely generated up to radical, then some member of
the chain is as well. -/
@[stacks 0G2Z "chain condition for finite generation up to radical"]
theorem exists_mem_fgUpToRadical_of_sSup
    {C : Set (Ideal R)} (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty)
    (hsSup : (sSup C).FGUpToRadical) :
    ∃ J ∈ C, J.FGUpToRadical := by
  classical
  rcases hsSup.exists_fg_le with ⟨K, hKfg, hKle, hKrad⟩
  obtain ⟨G, hG⟩ := hKfg
  obtain ⟨J, hJ, hGJ⟩ : ∃ J ∈ C, (G : Set R) ⊆ (J : Set R) := by
    refine hC.directedOn.exists_mem_subset_of_finset_subset_biUnion hCne ?_
    intro x hx
    have hxsSup : x ∈ sSup C := hKle (by rw [← hG]; exact subset_span hx)
    simpa only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] using
      (Submodule.mem_sSup_of_directed hCne hC.directedOn).1 hxsSup
  have hKJ : K ≤ J := by
    rw [← hG]
    exact span_le.2 hGJ
  refine ⟨J, hJ, K, ⟨G, hG⟩, ?_⟩
  apply le_antisymm
  · exact (radical_mono (le_sSup hJ)).trans_eq hKrad
  · exact radical_mono hKJ

/-- Ideals finitely generated up to radical form an Oka family. -/
@[stacks 0G2Z "finite generation up to radical is an Oka property"]
theorem isOka_fgUpToRadical : IsOka (fun I : Ideal R ↦ I.FGUpToRadical) where
  top := (fg_top R).fgUpToRadical
  oka {I} {a} hsup hcolon := by
    rcases hsup with ⟨J, hJfg, hJrad⟩
    rcases hcolon with ⟨K, hKfg, hKrad⟩
    refine ⟨J * K, hJfg.mul hKfg, ?_⟩
    calc
      I.radical = ((I ⊔ span ({a} : Set R)) * I.colon (span ({a} : Set R))).radical :=
        (radical_sup_mul_colon I (span ({a} : Set R))).symm
      _ = (I ⊔ span ({a} : Set R)).radical ⊓
            (I.colon (span ({a} : Set R))).radical := by
        rw [Ideal.radical_mul]
      _ = J.radical ⊓ K.radical := by
        rw [hJrad, hKrad]
      _ = (J * K).radical := by
        rw [Ideal.radical_mul]

end Ideal
