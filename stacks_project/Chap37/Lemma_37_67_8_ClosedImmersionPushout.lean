/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
