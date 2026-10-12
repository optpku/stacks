/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Remark_88_2_3_Base_change_Comparison
import StacksCheckRecall

/-!
# Remark 88.2.3 (Base change)

A ring map `φ : A1 → A2` with `φ(I1 ^ c) ⊆ I2` for some `c ≥ 1` induces the
systems functor of 88.2.3.1 and, when `I2` is finitely generated, the completed
functor of 88.2.3.2. The two functors agree via `toAdicSystem`.
-/

@[expose] public section

open CategoryTheory

universe u

/- Remark 88.2.3 (Base change) (1) A ring map `φ : A1 →+* A2` and ideals `Iᵢ`
with `φ(I1 ^ c) ⊆ I2` for some `c ≥ 1` induce stage maps
`A1 ⧸ I1 ^ (c * n) → A2 ⧸ I2 ^ n` and a systems base-change functor
`C1 ⥤ C2`, `(Bn) ↦ (B (c * n) ⊗[A1 ⧸ I1 ^ (c * n)] (A2 ⧸ I2 ^ n))`. -/
@[stacks 0AL5] #check AdicAlgebraSystem.baseChange

/- Remark 88.2.3 (Base change) (2) If `I2` is finitely generated, there is a
completed base-change functor `C1' ⥤ C2'` sending `B` to `(B ⊗[A1] A2)^∧`,
because the completion is complete by Algebra, Lemma 10.96.3. -/
@[stacks 0AL5] #check CommAlgCat.TopologicallyFiniteType.baseChange

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

namespace AdicCompleteFiniteType

/-- Remark 88.2.3 (Base change) (3) If both `I1` and `I2` are finitely generated,
the two base-change functors agree via `toAdicSystem`, which are equivalences by
Lemma 88.2.1. The comparison is the natural isomorphism of the square
`toAdicSystem I1 ⋙ systemsBaseChange ≅ completedBaseChange ⋙ toAdicSystem I2`;
completed base change uses `I2.FG` because the completion is complete by
Algebra, Lemma 10.96.3. -/
@[stacks 0AL5]
noncomputable abbrev baseChangeToAdicSystemIso (I1 : Ideal A1) (I2 : Ideal A2)
    {c : ℕ} (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG) :=
  CommAlgCat.TopologicallyFiniteType.baseChangeToAdicSystemIso I1 I2 hc hI hI2

/-- Components of the comparison isomorphism are `baseChangeObjIso`. -/
theorem baseChangeToAdicSystemIso_app (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A1 I1) :
    (baseChangeToAdicSystemIso I1 I2 hc hI hI2).app B =
      CommAlgCat.TopologicallyFiniteType.baseChangeObjIso I1 I2 hc hI hI2 B :=
  sorry

end AdicCompleteFiniteType
