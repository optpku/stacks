module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Rank
public import ReasLib.RingTheory.Depth

@[expose] public section

/-!
# Rank-minor criteria for injective coordinate maps

This leaf characterizes injectivity of a map between standard finite free
modules over a local ring through its exterior rank and rank-minor ideal.

@stack 00MX
-/

universe u

namespace LinearMap.RankMinorIdeal

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {m n : ℕ}

/-- Lemma 15.15.6, clauses (1) and (2), tag `00MX`: a coordinate map over a
local ring is injective exactly when it has full exterior rank and its
rank-minor ideal has zero annihilator. -/
@[stacks 00MX "(1) iff (2)"]
theorem injective_iff_fullRank_and_annihilator_eq_bot
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      LinearMap.exteriorRank φ = m ∧
        (I(φ)).annihilator = (⊥ : Ideal R) := sorry
-- Proof strategy: for the forward implication, localize at a weakly associated prime of the
-- annihilator of the maximal-minor ideal, identify the localized map with the mapped coordinate
-- matrix, and use the preceding universal-injectivity criterion on the closed fiber to contradict
-- vanishing of all maximal minors.  Convert the resulting maximal-minor statement to
-- `exteriorRank` and `I(φ)`.  Conversely use Cramer's rule for maximal minors: each coordinate of
-- a kernel vector is annihilated by `I(φ)`, hence is zero by the annihilator hypothesis.

/-- A Noetherian local companion to Lemma 15.15.6: injectivity is equivalent
to full exterior rank and positive depth of the rank-minor ideal. -/
@[stacks 00MX "positive-depth companion"]
theorem injective_iff_fullRank_and_one_le_depth
    [IsNoetherianRing R] (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      LinearMap.exteriorRank φ = m ∧
        (1 : WithTop ℕ) ≤ (I(φ)).depth R := sorry
-- Proof strategy: rewrite with `injective_iff_fullRank_and_annihilator_eq_bot`; in a Noetherian
-- local ring prove `I.annihilator = ⊥ ↔ 1 ≤ I.depth R` using the associated-prime criterion for a
-- regular element and `Ideal.natCast_le_depth_self_iff` from
-- `ReasLib.RingTheory.Depth.RegularSequence`.

/-- Lemma 15.15.6, clauses (1) and (3), tag `00MX`: over a Noetherian local
ring, a coordinate map is injective exactly when it has full exterior rank
and its rank-minor ideal is the unit ideal or contains a nonzerodivisor. -/
@[stacks 00MX "(1) iff (3)"]
theorem injective_iff_fullRank_and_eq_top_or_exists_isRegular
    [IsNoetherianRing R] (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      LinearMap.exteriorRank φ = m ∧
        (I(φ) = ⊤ ∨ ∃ x ∈ I(φ), IsRegular x) := sorry
-- Proof strategy: combine `injective_iff_fullRank_and_one_le_depth` with the length-one case of
-- `Ideal.natCast_le_depth_self_iff`, which identifies `1 ≤ I.depth R` with either `I = ⊤` or a
-- one-element regular sequence, and unpack that sequence as an element `x ∈ I` with
-- `IsRegular x`.

end LinearMap.RankMinorIdeal
