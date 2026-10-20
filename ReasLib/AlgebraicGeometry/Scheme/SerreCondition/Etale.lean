/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.satisfiesSerreConditionS

/-- For every `k`, being locally Noetherian and satisfying `(S_k)` is local for the
étale precoverage. -/
instance isLocalEtale (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ IsLocallyNoetherian X ∧ Scheme.satisfiesSerreConditionS X k)
      Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Scheme.satisfiesSerreConditionS

namespace AlgebraicGeometry.Scheme.satisfiesSerreConditionR

/-- For every `k`, being locally Noetherian and satisfying `(R_k)` is local for the
étale precoverage. -/
instance isLocalEtale (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦
        AlgebraicGeometry.IsLocallyNoetherian X ∧
          AlgebraicGeometry.Scheme.satisfiesSerreConditionR X k)
      Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Scheme.satisfiesSerreConditionR
