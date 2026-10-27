/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.HilbertSamuel.SupportDim
public import ReasLib.RingTheory.RegularLocalRing.Parameters

@[expose] public section

/-!
# Dimension of a Noetherian Local Ring

@stack 00KQ
@stack 00P6

This module specializes the module-level comparison
`Ideal.HilbertSamuel.map_degree_eq_supportDim` to a local ring and relates the
result to ideals of definition and systems of parameters.  Bounds by
`spanFinrank`, natural-valued equivalences, and the source-facing TFAE are
exposed as separate reusable views.
-/

universe u

open IsLocalRing

namespace Ideal.IsIdealOfDefinition

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- An ideal of definition bounds the Krull dimension by its minimal number
of generators. -/
@[stacks 00KQ "dimension bound by an ideal of definition"]
theorem ringKrullDim_le_spanFinrank {I : Ideal R}
    (hI : I.IsIdealOfDefinition) :
    ringKrullDim R ≤ I.spanFinrank := by
  have hIm : I ≤ maximalIdeal R := I.le_radical.trans_eq hI
  have hne : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIm
  have hheight : I.height = (maximalIdeal R).height := by
    rw [Ideal.height_eq_inf_minimalPrimes, ← I.radical_minimalPrimes, hI]
    simp [Ideal.minimalPrimes_eq_subsingleton_self]
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr (hheight ▸ I.height_le_spanFinrank hne)

/-- An ideal of definition bounds the Hilbert--Samuel degree by its minimal
number of generators. -/
@[stacks 00KQ "Hilbert-Samuel degree bound by an ideal of definition"]
theorem hilbertSamuelDegree_le_spanFinrank {I : Ideal R}
    (hI : I.IsIdealOfDefinition) :
    Ideal.HilbertSamuel.degree R R ≤ I.spanFinrank := by
  apply (Nat.castOrderEmbedding : ℕ ↪o ℕ∞).withBotMap.le_iff_le.mp
  simpa [Ideal.HilbertSamuel.map_degree_eq_supportDim,
    Module.supportDim_self_eq_ringKrullDim] using hI.ringKrullDim_le_spanFinrank

end Ideal.IsIdealOfDefinition

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A parameter family whose span is an ideal of definition bounds the Krull
dimension by the length of that family. -/
@[stacks 00KQ "dimension bound by a parameter family"]
theorem ringKrullDim_le_of_parameterIdeal {d : ℕ}
    {x : Fin d → maximalIdeal R}
    (hx : (parameterIdeal x).IsIdealOfDefinition) :
    ringKrullDim R ≤ d := by
  have hgen : (parameterIdeal x).spanFinrank ≤ d := by
    change (Submodule.span R (Set.range fun i ↦ (x i : R))).spanFinrank ≤ d
    apply ENat.coe_le_coe.mp
    exact (Submodule.spanFinrank_span_le_encard _).trans
      (by simpa using Set.encard_image_le (fun i ↦ (x i : R)) Set.univ)
  exact hx.ringKrullDim_le_spanFinrank.trans (by exact_mod_cast hgen)

/-- A finite family generating an ideal of definition gives the same dimension
bound when the family is presented existentially. -/
@[stacks 00KQ "dimension bound from an existential parameter family"]
theorem ringKrullDim_le_of_exists_parameterIdeal {d : ℕ}
    (h : ∃ x : Fin d → maximalIdeal R,
      (parameterIdeal x).IsIdealOfDefinition) :
    ringKrullDim R ≤ d := by
  obtain ⟨x, hx⟩ := h
  exact ringKrullDim_le_of_parameterIdeal hx

/-- Systems of parameters of length `d` exist exactly when the Krull
dimension is `d`. -/
@[stacks 00KQ "systems of parameters and dimension"]
theorem exists_systemOfParameters_iff_ringKrullDim_eq (d : ℕ) :
    (∃ x : Fin d → maximalIdeal R, IsSystemOfParameters x) ↔
      ringKrullDim R = d := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    exact hx.1
  · intro hdim
    obtain ⟨s, hs, hcard⟩ :=
      (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing
    have hsd : s.card = d := by
      have hh : ((s.card : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) :=
        (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hcard).trans
          (maximalIdeal_height_eq_ringKrullDim.trans hdim)
      exact_mod_cast hh
    let e := s.equivFinOfCardEq hsd
    let x : Fin d → maximalIdeal R := fun i ↦
      ⟨(e.symm i : R), hs.le (Ideal.subset_span (e.symm i).property)⟩
    have hx : parameterIdeal x = Ideal.span (s : Set R) := by
      change Ideal.span _ = Ideal.span _
      congr 1
      ext r
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).property
      · intro hr
        exact ⟨e ⟨r, hr⟩, by simp [x]⟩
    refine ⟨x, hdim, ?_⟩
    change (parameterIdeal x).radical = maximalIdeal R
    rw [hx, Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hs.le, inferInstance⟩
    · apply le_sInf
      rintro q ⟨hsq, hq⟩
      exact hs.2 ⟨hq, hsq⟩ (le_maximalIdeal hq.ne_top)

/-- A natural-valued Krull dimension is realized by a system of parameters of
that length. -/
@[stacks 00KQ "existence of a system of parameters"]
theorem exists_systemOfParameters_of_ringKrullDim_eq {d : ℕ}
    (hdim : ringKrullDim R = d) :
    ∃ x : Fin d → maximalIdeal R, IsSystemOfParameters x := by
  exact (exists_systemOfParameters_iff_ringKrullDim_eq d).mpr hdim

/-- An ambient natural-valued Krull dimension admits a parameter family whose
generated ideal is an ideal of definition. -/
@[stacks 00KQ "ideal-of-definition parameter family"]
theorem exists_parameterIdeal_of_ringKrullDim_eq {d : ℕ}
    (hdim : ringKrullDim R = d) :
    ∃ x : Fin d → maximalIdeal R,
      (parameterIdeal x).IsIdealOfDefinition := by
  obtain ⟨x, hx⟩ := exists_systemOfParameters_of_ringKrullDim_eq hdim
  exact ⟨x, hx.2⟩

/-- No family shorter than the Krull dimension can generate an ideal of
definition. -/
@[stacks 00KQ "minimal number of parameters"]
theorem not_exists_parameterIdeal_of_lt_ringKrullDim
    {d n : ℕ} (hdim : ringKrullDim R = d) (hn : n < d) :
    ¬ ∃ x : Fin n → maximalIdeal R,
      (parameterIdeal x).IsIdealOfDefinition := by
  intro h
  have hle := ringKrullDim_le_of_exists_parameterIdeal h
  rw [hdim] at hle
  exact (not_le_of_gt hn) (by exact_mod_cast hle)

end IsLocalRing

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The module-level equality `map_degree_eq_supportDim`, specialized to the
ring as a module over itself, identifies Hilbert--Samuel degree with Krull
dimension. -/
@[stacks 00KQ "Krull dimension equals Hilbert-Samuel degree"]
theorem map_degree_eq_ringKrullDim :
    Nat.castOrderEmbedding.withBotMap (degree R R) = ringKrullDim R := by
  exact map_degree_eq_supportDim.trans (Module.supportDim_self_eq_ringKrullDim R)

/-- The Krull dimension is bounded by the transported Hilbert--Samuel degree. -/
@[stacks 00KQ "Krull dimension bounded by Hilbert-Samuel degree"]
theorem ringKrullDim_le_degree :
    ringKrullDim R ≤ Nat.castOrderEmbedding.withBotMap (degree R R) := by
  exact map_degree_eq_ringKrullDim.symm.le

/-- A natural number is the Hilbert--Samuel degree exactly when it is the
Krull dimension. -/
@[stacks 00KQ "natural Hilbert-Samuel degree characterization"]
theorem degree_eq_iff_ringKrullDim_eq (d : ℕ) :
    degree R R = d ↔ ringKrullDim R = d := by
  rw [← map_degree_eq_ringKrullDim]
  exact Nat.castOrderEmbedding.withBotMap.injective.eq_iff.symm

/-- Any eventual polynomial representative of the maximal-ideal
Hilbert--Samuel `φ`-function computes Krull dimension by the successor of its
degree. -/
@[stacks 00P6 "local dimension from an eventual Hilbert polynomial"]
theorem ringKrullDim_eq_degree_succ_of_eventuallyEq_phi
    (P : Polynomial ℚ)
    (hP : P.EventuallyEqNat (fun n ↦
      ((Ideal.hilbertSamuelPhi (maximalIdeal R) R n).toNat : ℚ))) :
    ringKrullDim R = P.degree.succ := sorry

/-- The selected maximal-ideal `φ`-polynomial computes the Krull dimension of
a Noetherian local ring without requiring an auxiliary polynomial argument. -/
@[stacks 00P6 "local dimension from the Hilbert-Samuel phi polynomial"]
theorem ringKrullDim_eq_phiPolynomial_degree_succ :
    ringKrullDim R =
      (phiPolynomial (maximalIdeal R) R).degree.succ := by
  exact ringKrullDim_eq_degree_succ_of_eventuallyEq_phi _
    (phiPolynomial_spec_maximalIdeal (M := R))

/-- A parameter family whose span is an ideal of definition bounds the
Hilbert--Samuel degree by the length of that family. -/
@[stacks 00KQ "Hilbert-Samuel degree bound by a parameter family"]
theorem degree_le_of_parameterIdeal {d : ℕ}
    {x : Fin d → maximalIdeal R}
    (hx : (parameterIdeal x).IsIdealOfDefinition) :
    degree R R ≤ d := by
  apply (Nat.castOrderEmbedding : ℕ ↪o ℕ∞).withBotMap.le_iff_le.mp
  simpa [map_degree_eq_ringKrullDim] using ringKrullDim_le_of_parameterIdeal hx

/-- Proposition 10.60.9 (Tag 00KQ): Krull dimension, Hilbert--Samuel degree,
and the minimal number of generators of an ideal of definition agree. -/
@[stacks 00KQ]
theorem dimension_tfae (d : ℕ) :
    List.TFAE
      [ ringKrullDim R = d
      , degree R R = d
      , (∃ x : Fin d → maximalIdeal R,
          (parameterIdeal x).IsIdealOfDefinition) ∧
          ∀ n : ℕ, n < d →
            ¬ ∃ x : Fin n → maximalIdeal R,
              (parameterIdeal x).IsIdealOfDefinition
      ] := by
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  refine ⟨(degree_eq_iff_ringKrullDim_eq d).symm, ?_, List.tfae_singleton _⟩
  rw [degree_eq_iff_ringKrullDim_eq]
  constructor
  · intro hdim
    exact ⟨exists_parameterIdeal_of_ringKrullDim_eq hdim,
      fun n hn ↦ not_exists_parameterIdeal_of_lt_ringKrullDim hdim hn⟩
  · rintro ⟨hex, hmin⟩
    obtain ⟨n, hn⟩ := (maximalIdeal R).height_ne_top_of_isPrime |> ENat.ne_top_iff_exists.mp
    have hdim : ringKrullDim R = n :=
      maximalIdeal_height_eq_ringKrullDim.symm.trans (congrArg WithBot.some hn.symm)
    have hnd : n ≤ d := by
      have hle := ringKrullDim_le_of_exists_parameterIdeal hex
      rw [hdim] at hle
      exact_mod_cast hle
    have hdn : d ≤ n := by
      by_contra h
      exact hmin n (Nat.lt_of_not_ge h) (exists_parameterIdeal_of_ringKrullDim_eq hdim)
    exact hdim.trans (by exact_mod_cast Nat.le_antisymm hnd hdn)

end Ideal.HilbertSamuel

namespace IsLocalRing.IsSystemOfParameters

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A system of parameters has Hilbert--Samuel degree equal to the length of
the parameter family. -/
@[stacks 00KQ "Hilbert-Samuel degree of a system of parameters"]
theorem hilbertSamuelDegree_eq_length {d : ℕ}
    {x : Fin d → maximalIdeal R}
    (hx : IsSystemOfParameters x) :
    Ideal.HilbertSamuel.degree R R = d := by
  exact (Ideal.HilbertSamuel.degree_eq_iff_ringKrullDim_eq d).mpr hx.1

end IsLocalRing.IsSystemOfParameters
