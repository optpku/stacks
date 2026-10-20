/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.Limits.pullback

variable {C : Type u} [Category.{v} C] {Y Z Z' X : C}
variable (yZ : Y ⟶ Z) (z'Z : Z' ⟶ Z) (f : X ⟶ Z)
variable [HasPullback yZ z'Z] [HasPullback f z'Z] [HasPullback yZ f]
variable [HasPullback (pullback.snd yZ z'Z) (pullback.snd f z'Z)]

/-- The canonical comparison from the iterated pullback over `Z'` to the pullback over `Z`,
induced by the projections to `Y` and `X`. -/
def cubeMap :
    pullback (pullback.snd yZ z'Z) (pullback.snd f z'Z) ⟶ pullback yZ f :=
  pullback.map (pullback.snd yZ z'Z) (pullback.snd f z'Z) yZ f
    (pullback.fst yZ z'Z) (pullback.fst f z'Z) z'Z
    pullback.condition.symm pullback.condition.symm

/-- The first projection of the iterated-pullback comparison is the composite projection
to `Y`. -/
theorem cubeMap_fst :
    cubeMap yZ z'Z f ≫ pullback.fst yZ f =
      pullback.fst (pullback.snd yZ z'Z) (pullback.snd f z'Z) ≫ pullback.fst yZ z'Z := sorry

/-- The second projection of the iterated-pullback comparison is the composite projection
to `X`. -/
theorem cubeMap_snd :
    cubeMap yZ z'Z f ≫ pullback.snd yZ f =
      pullback.snd (pullback.snd yZ z'Z) (pullback.snd f z'Z) ≫ pullback.fst f z'Z := sorry

/-- The iterated-pullback comparison and the projection to `Y ×_Z Z'` form a cartesian
square over `Y`. -/
theorem cubeMap_fst_isPullback :
    IsPullback (pullback.fst (pullback.snd yZ z'Z) (pullback.snd f z'Z))
      (cubeMap yZ z'Z f) (pullback.fst yZ z'Z) (pullback.fst yZ f) := sorry

/-- The iterated-pullback comparison and the projection to `X ×_Z Z'` form a cartesian
square over `X`. -/
theorem cubeMap_snd_isPullback :
    IsPullback (cubeMap yZ z'Z f)
      (pullback.snd (pullback.snd yZ z'Z) (pullback.snd f z'Z))
      (pullback.snd yZ f) (pullback.fst f z'Z) := sorry

end CategoryTheory.Limits.pullback
