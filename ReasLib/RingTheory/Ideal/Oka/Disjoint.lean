/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Oka
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideals Meeting a Submonoid as an Oka Family

@stack 05KA
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- Ideals meeting a fixed submonoid form an Oka family. -/
@[stacks 05KA "ideals meeting a submonoid form an Oka family"]
theorem isOka_not_disjoint (S : Submonoid R) :
    IsOka (fun I : Ideal R ↦ ¬ Disjoint (I : Set R) S) where
  top := by
    rw [Set.not_disjoint_iff_nonempty_inter]
    exact ⟨1, by simp⟩
  oka {I} {a} hsup hcolon := by
    rw [Set.not_disjoint_iff_nonempty_inter] at hsup hcolon ⊢
    rcases hsup with ⟨s, hsI, hsS⟩
    rcases hcolon with ⟨t, htI, htS⟩
    rcases mem_span_singleton_sup.mp (by simpa [sup_comm] using hsI) with ⟨r, i, hiI, hsi⟩
    refine ⟨t * s, ?_, S.mul_mem htS hsS⟩
    rw [← hsi, mul_add]
    refine I.add_mem ?_ (I.mul_mem_left t hiI)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      I.mul_mem_left r (mem_colon_span_singleton.mp htI)

end Ideal
