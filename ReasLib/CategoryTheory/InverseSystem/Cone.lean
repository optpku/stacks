/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Cones over Sequential Inverse Systems

This leaf provides stagewise notation and tail restriction for cones over sequential inverse
systems. Tail restriction is the existing `Limits.Cone.whisker` construction applied to the
canonical tail reindexing functor, so no second cone naturality datum is introduced.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Limits.Cone

variable {A : Type u} [Category.{v} A] {K : SequentialInverseSystem A}

/-- The map from the vertex of a cone over a sequential inverse system to its `i`th stage. -/
def stageMap (s : Cone K) (i : ℕ) : s.pt ⟶ K.obj (Opposite.op i) :=
  s.π.app (Opposite.op i)

/-- The stage maps of a cone commute with every transition map of the sequential inverse
system. -/
@[reassoc]
theorem stageMap_naturality (s : Cone K) {i j : ℕ} (hij : i ≤ j) :
    s.stageMap j ≫ K.transitionMap hij = s.stageMap i := sorry

/-- The stage maps of a cone commute with each successor transition. -/
@[reassoc]
theorem stageMap_step (s : Cone K) (i : ℕ) :
    s.stageMap (i + 1) ≫ K.stepMap i = s.stageMap i := sorry

/-- Restrict a cone over a sequential inverse system to the tail beginning at `n`. -/
def shift (s : Cone K) (n : ℕ) : Cone (K.shift n) :=
  s.whisker (SequentialInverseSystem.tailFunctor n)

/-- Restricting a cone to a tail leaves its vertex unchanged. -/
@[simp]
theorem shift_pt (s : Cone K) (n : ℕ) :
    (s.shift n).pt = s.pt := sorry

/-- The `i`th leg of a shifted cone is the original leg at stage `n + i`. -/
@[simp]
theorem shift_π_app (s : Cone K) (n i : ℕ) :
    (s.shift n).π.app (Opposite.op i) =
      s.π.app (Opposite.op (n + i)) := sorry

/-- The `i`th stage map of a shifted cone is the original stage map at `n + i`. -/
@[simp]
theorem shift_stageMap (s : Cone K) (n i : ℕ) :
    (s.shift n).stageMap i = s.stageMap (n + i) := sorry

end CategoryTheory.Limits.Cone
