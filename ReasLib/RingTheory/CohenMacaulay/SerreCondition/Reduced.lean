/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduced Rings and Serre Conditions

This leaf owns the low-degree equivalence between reducedness and `(R₀)`, `(S₁)` for Noetherian
commutative rings.  The conditions themselves remain the parameterized owners from
`CohenMacaulay.SerreCondition`.
-/

@[expose] public section

universe u

notation:max R:max " ⊧ " "(" "R₀" ")" => SerreConditionR R 0
notation:max R:max " ⊧ " "(" "S₁" ")" => SerreConditionS R 1

variable {R : Type u} [CommRing R]

namespace IsReduced

/-- A reduced Noetherian ring satisfies Serre's condition `(R₀)`. -/
@[stacks 031R "reduced rings satisfy R₀"]
instance serreConditionR_zero [IsNoetherianRing R] [IsReduced R] : R ⊧ (R₀) := sorry

/-- A reduced Noetherian ring satisfies Serre's condition `(S₁)`. -/
@[stacks 031R "reduced rings satisfy S₁"]
instance serreConditionS_one [IsNoetherianRing R] [IsReduced R] : R ⊧ (S₁) := sorry

/-- Serre's conditions `(R₀)` and `(S₁)` imply reducedness for a Noetherian ring. -/
@[stacks 031R "reducedness from R₀ and S₁"]
theorem of_serre (hR : R ⊧ (R₀)) (hS : R ⊧ (S₁)) : IsReduced R := sorry

/-- A Noetherian commutative ring is reduced exactly when it satisfies `(R₀)` and `(S₁)`. -/
@[stacks 031R "reducedness and Serre conditions"]
theorem iff_serre [IsNoetherianRing R] :
    IsReduced R ↔ R ⊧ (R₀) ∧ R ⊧ (S₁) := sorry

end IsReduced
