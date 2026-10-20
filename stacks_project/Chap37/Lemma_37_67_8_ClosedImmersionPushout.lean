/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Compatibility check for the canonical pushout of two closed immersions. -/
#check (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.instHasPushout :
  ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j],
    HasPushout i j)
