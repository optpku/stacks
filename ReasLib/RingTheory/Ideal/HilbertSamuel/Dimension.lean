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
    ringKrullDim R ≤ I.spanFinrank := sorry

/-- An ideal of definition bounds the Hilbert--Samuel degree by its minimal
number of generators. -/
@[stacks 00KQ "Hilbert-Samuel degree bound by an ideal of definition"]
theorem hilbertSamuelDegree_le_spanFinrank {I : Ideal R}
    (hI : I.IsIdealOfDefinition) :
    Ideal.HilbertSamuel.degree R R ≤ I.spanFinrank := sorry

end Ideal.IsIdealOfDefinition

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A parameter family whose span is an ideal of definition bounds the Krull
dimension by the length of that family. -/
@[stacks 00KQ "dimension bound by a parameter family"]
theorem ringKrullDim_le_of_parameterIdeal {d : ℕ}
    {x : Fin d → maximalIdeal R}
    (hx : (parameterIdeal x).IsIdealOfDefinition) :
    ringKrullDim R ≤ d := sorry

/-- A finite family generating an ideal of definition gives the same dimension
bound when the family is presented existentially. -/
@[stacks 00KQ "dimension bound from an existential parameter family"]
theorem ringKrullDim_le_of_exists_parameterIdeal {d : ℕ}
    (h : ∃ x : Fin d → maximalIdeal R,
      (parameterIdeal x).IsIdealOfDefinition) :
    ringKrullDim R ≤ d := sorry

/-- Systems of parameters of length `d` exist exactly when the Krull
dimension is `d`. -/
@[stacks 00KQ "systems of parameters and dimension"]
theorem exists_systemOfParameters_iff_ringKrullDim_eq (d : ℕ) :
    (∃ x : Fin d → maximalIdeal R, IsSystemOfParameters x) ↔
      ringKrullDim R = d := sorry

/-- A natural-valued Krull dimension is realized by a system of parameters of
that length. -/
@[stacks 00KQ "existence of a system of parameters"]
theorem exists_systemOfParameters_of_ringKrullDim_eq {d : ℕ}
    (hdim : ringKrullDim R = d) :
    ∃ x : Fin d → maximalIdeal R, IsSystemOfParameters x := sorry

/-- An ambient natural-valued Krull dimension admits a parameter family whose
generated ideal is an ideal of definition. -/
@[stacks 00KQ "ideal-of-definition parameter family"]
theorem exists_parameterIdeal_of_ringKrullDim_eq {d : ℕ}
    (hdim : ringKrullDim R = d) :
    ∃ x : Fin d → maximalIdeal R,
      (parameterIdeal x).IsIdealOfDefinition := sorry

/-- No family shorter than the Krull dimension can generate an ideal of
definition. -/
@[stacks 00KQ "minimal number of parameters"]
theorem not_exists_parameterIdeal_of_lt_ringKrullDim
    {d n : ℕ} (hdim : ringKrullDim R = d) (hn : n < d) :
    ¬ ∃ x : Fin n → maximalIdeal R,
      (parameterIdeal x).IsIdealOfDefinition := sorry

end IsLocalRing

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The module-level equality `map_degree_eq_supportDim`, specialized to the
ring as a module over itself, identifies Hilbert--Samuel degree with Krull
dimension. -/
@[stacks 00KQ "Krull dimension equals Hilbert-Samuel degree"]
theorem map_degree_eq_ringKrullDim :
    Nat.castOrderEmbedding.withBotMap (degree R R) = ringKrullDim R := sorry

/-- The Krull dimension is bounded by the transported Hilbert--Samuel degree. -/
@[stacks 00KQ "Krull dimension bounded by Hilbert-Samuel degree"]
theorem ringKrullDim_le_degree :
    ringKrullDim R ≤ Nat.castOrderEmbedding.withBotMap (degree R R) := sorry

/-- A natural number is the Hilbert--Samuel degree exactly when it is the
Krull dimension. -/
@[stacks 00KQ "natural Hilbert-Samuel degree characterization"]
theorem degree_eq_iff_ringKrullDim_eq (d : ℕ) :
    degree R R = d ↔ ringKrullDim R = d := sorry

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
      (phiPolynomial (maximalIdeal R) R).degree.succ := sorry

/-- A parameter family whose span is an ideal of definition bounds the
Hilbert--Samuel degree by the length of that family. -/
@[stacks 00KQ "Hilbert-Samuel degree bound by a parameter family"]
theorem degree_le_of_parameterIdeal {d : ℕ}
    {x : Fin d → maximalIdeal R}
    (hx : (parameterIdeal x).IsIdealOfDefinition) :
    degree R R ≤ d := sorry

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
      ] := sorry

end Ideal.HilbertSamuel

namespace IsLocalRing.IsSystemOfParameters

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A system of parameters has Hilbert--Samuel degree equal to the length of
the parameter family. -/
@[stacks 00KQ "Hilbert-Samuel degree of a system of parameters"]
theorem hilbertSamuelDegree_eq_length {d : ℕ}
    {x : Fin d → maximalIdeal R}
    (hx : IsSystemOfParameters x) :
    Ideal.HilbertSamuel.degree R R = d := sorry

end IsLocalRing.IsSystemOfParameters
