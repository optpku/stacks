/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Special fiber of a proper flat formal system

The closed subset `X_0 ⊂ |X|` consists of the points of the limit space that
lie over `Spec(A_n) ⊂ Spec(A)`. This image is independent of the stage `n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The closed subset `X_0 ⊂ |X|` of points of the limit space lying over the
closed subset `Spec(A_n) ⊂ Spec(A)`, realized as the preimage of the image of
`stageSpecToBase` at stage `0`. -/
def specialFiberPoints (S : ProperFlatFormalSystem) : Set (Points S.space) :=
  (Points.map (SchemeRealization.toBase S.space)) ⁻¹'
    Set.range (Points.map (stageSpecToBase S.limitCone 0))

/-- `specialFiberPoints` is the preimage of `|Spec(A_0)|` along `|X| → |Spec(A)|`. -/
theorem specialFiberPoints_eq (S : ProperFlatFormalSystem) :
    specialFiberPoints S =
      (Points.map (SchemeRealization.toBase S.space)) ⁻¹'
        Set.range (Points.map (stageSpecToBase S.limitCone 0)) :=
  sorry

/-- A point of `|X|` lies in `specialFiberPoints` if and only if it maps to a point of
`Spec(A_0)` in `|Spec(A)|`. -/
theorem mem_specialFiberPoints (S : ProperFlatFormalSystem) {x : Points S.space} :
    x ∈ specialFiberPoints S ↔
      Points.map (SchemeRealization.toBase S.space) x ∈
        Set.range (Points.map (stageSpecToBase S.limitCone 0)) :=
  sorry

/-- The special fiber `X_0 ⊂ |X|` is closed in the canonical topology. -/
theorem isClosed_specialFiberPoints (S : ProperFlatFormalSystem) :
    IsClosed (specialFiberPoints S) :=
  sorry

/-- The images of `|Spec(A_m)|` and `|Spec(A_n)|` in `|Spec(A)|` coincide. -/
theorem stageSpectrumPoints_independent (S : ProperFlatFormalSystem) (m n : ℕ) :
    Set.range (Points.map (stageSpecToBase S.limitCone m)) =
      Set.range (Points.map (stageSpecToBase S.limitCone n)) :=
  sorry

/-- The special fiber equals the image of each finite-stage closed subspace `|X_n| → |X|`. -/
theorem specialFiberPoints_eq_stage (S : ProperFlatFormalSystem) (n : ℕ) :
    specialFiberPoints S = (S.stageClosedSubspace n).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
