/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.SerreCondition
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Normal

/-!
# Cohen–Macaulay Normal Schemes

This file relates normality and dimension bounds to the Cohen–Macaulay property for locally
Noetherian schemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- A locally Noetherian normal scheme of topological Krull dimension at most two is
Cohen–Macaulay. -/
theorem cohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two
    (hnormal : X.isNormal) (hdim : topologicalKrullDim X ≤ 2) :
    CohenMacaulay X := by
  refine (cohenMacaulay_iff_forall_satisfiesSerreConditionS X).2 ?_
  intro k
  rw [satisfiesSerreConditionS_iff]
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X] at hdim
  have hS2 : satisfiesSerreConditionS X 2 :=
    satisfiesSerreConditionS_two_of_isNormal X hnormal
  intro x
  have hsupp :
      Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x) ≤ (2 : WithBot ℕ∞) := by
    rw [Module.supportDim_self_eq_ringKrullDim]
    exact (le_iSup (fun y ↦ ringKrullDim (X.presheaf.stalk y)) x).trans hdim
  have hdepth :
      Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x) ≤
        WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) := by
    simpa [min_eq_right hsupp] using ((satisfiesSerreConditionS_iff X 2).1 hS2 x)
  exact le_trans (min_le_right (k : WithBot ℕ∞) _) hdepth

end AlgebraicGeometry.Scheme
