/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import AnnalsChallenge.Definitions.AlgebraicJacobian

/-!
# Main Statement from Uniformity in Mordell–Lang for curves

We formalise the statement of the main result from V. Dimitrov, Z. Gao, and P. Habegger,
`Uniformity in Mordell–Lang for curves`, Annals of Math, 194 (1) 2021.
-/

@[expose] public section

namespace UniformMordellLang

open CommGroup Module CategoryTheory MonoidalCategory AlgebraicGeometry JacobianChallenge

/-- A positive bound valid for every number field of bounded degree and every
smooth proper geometrically irreducible curve of the prescribed genus.

This predicate uses small fields to define a single numerical constant with
no universe parameter. `theorem_1_1` below retains the original universe-polymorphic
statement; passage to a small model of a number field is a proof obligation. -/
def IsUniformBound (g d B : ℕ) : Prop :=
  1 ≤ B ∧ ∀ (F : Type) [Field F] [NumberField F]
    (_hF : finrank ℚ F ≤ d) (C : Over (Spec (.of F))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (_hC : genus C = g),
    ENat.card (𝟙_ (Over (Spec (.of F))) ⟶ C) ≤
      B ^ (1 + freeRank (𝟙_ (Over (Spec (.of F))) ⟶ Jacobian C))

/-- The existential form of Theorem 1.1. Its deep mathematical proof is
outside the present statement-formalization task. -/
theorem exists_uniformBound (g d : ℕ) (hg : 2 ≤ g) (hd : 1 ≤ d) :
    ∃ B : ℕ, IsUniformBound g d B := by
  sorry

/-- The least positive uniform bound in the range of Theorem 1.1, and `1`
outside that range. It depends only on genus and the field-degree bound. -/
noncomputable def c (g d : ℕ) : ℕ := by
  classical
  exact if h : 2 ≤ g ∧ 1 ≤ d then Nat.find (exists_uniformBound g d h.1 h.2) else 1

theorem c_spec (g d : ℕ) (hg : 2 ≤ g) (hd : 1 ≤ d) :
    IsUniformBound g d (c g d) := by
  classical
  simpa only [c, dif_pos (And.intro hg hd)] using
    Nat.find_spec (exists_uniformBound g d hg hd)

theorem one_le_c (g d : ℕ) : 1 ≤ c g d := by
  classical
  by_cases h : 2 ≤ g ∧ 1 ≤ d
  · exact (c_spec g d h.1 h.2).1
  · simp only [c, dif_neg h, le_refl]

/-- Minimality makes the choice of constant precise; no explicit effective
numerical formula is claimed. -/
theorem c_min (g d B : ℕ) (hg : 2 ≤ g) (hd : 1 ≤ d)
    (hB : IsUniformBound g d B) : c g d ≤ B := by
  classical
  simpa only [c, dif_pos (And.intro hg hd)] using
    Nat.find_min' (exists_uniformBound g d hg hd) hB

/--
Statement of Theorem 1.1:

Let `g ≥ 2` and `d ≥ 1` be integers. Then there exists a constant `c = c(g, d) ≥ 1` with the
following property. If `C` is a smooth curve of genus `g` defined over a number field `F` with
`[F : Q] ≤ d`, then `#C(F) ≤ c^(1+ρ)`, where `ρ` is the rank of `Jac(C)(F)`.

The Jacobian is the representing scheme of the degree-zero relative Picard
functor, including when `C` has no `F`-point. Its pointed Albanese property is
available after a point is chosen. The bound is trivial when `C` has no `F`-points.
-/
theorem theorem_1_1 (g d : ℕ) (hg : g ≥ 2) (hd : d ≥ 1) {F : Type*} [Field F] [NumberField F]
    (hF : finrank ℚ F ≤ d) (C : Over (Spec (.of F))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] (hC : genus C = g) :
    ENat.card (𝟙_ (Over (Spec (.of F))) ⟶ C) ≤
      c g d ^ (1 + freeRank (𝟙_ (Over (Spec (.of F))) ⟶ Jacobian C)) := by
  sorry

/-- A version following the paper's existential quantifier, with positivity
included explicitly. The bound is independent of the curve and its field. -/
theorem theorem_1_1_exists (g d : ℕ) (hg : 2 ≤ g) (hd : 1 ≤ d) :
    ∃ B : ℕ, IsUniformBound g d B :=
  ⟨c g d, c_spec g d hg hd⟩

end UniformMordellLang
