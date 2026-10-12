/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition
public import ReasLib.RingTheory.Normal.Serre

/-!
# Normal Schemes and Serre's Criterion

This file relates normality of locally Noetherian schemes to the scheme-level and stalkwise
forms of Serre's conditions.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- A locally Noetherian scheme is normal exactly when it satisfies Serre's conditions `(S₂)`
and `(R₁)`. -/
theorem isNormal_iff_serre :
    X.isNormal ↔ satisfiesSerreConditionS X 2 ∧ satisfiesSerreConditionR X 1 := sorry

/-- A locally Noetherian scheme is normal exactly when it satisfies `(R₁)` and all of its
stalks satisfy the ring-theoretic condition `(S₂)`. -/
theorem isNormal_iff_serre_stalkwise :
    X.isNormal ↔
      satisfiesSerreConditionR X 1 ∧ ∀ x : X, (X.presheaf.stalk x) ⊧ (S₂) := by
  rw [isNormal_iff, satisfiesSerreConditionR_iff_stalkwise_serreConditionR]
  constructor
  · intro hX
    refine ⟨?_, ?_⟩
    · intro x
      exact (IsNormalRing.iff_serre.1 (hX x)).1
    · intro x
      exact (IsNormalRing.iff_serre.1 (hX x)).2
  · rintro ⟨hR, hS⟩ x
    exact IsNormalRing.iff_serre.2 ⟨hR x, hS x⟩

/-- A locally Noetherian normal scheme satisfies Serre's condition `(S₂)`. -/
theorem satisfiesSerreConditionS_two_of_isNormal
    (hnormal : X.isNormal) :
    satisfiesSerreConditionS X 2 :=
  ((isNormal_iff_serre X).1 hnormal).1

end AlgebraicGeometry.Scheme
