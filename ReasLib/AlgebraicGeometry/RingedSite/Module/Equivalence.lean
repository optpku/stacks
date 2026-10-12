/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of module categories on ringed sites

A ringed equivalence induces equivalences on both inverse and direct image of module sheaves.
This is the categorical bridge used by property-specific invariance results; those results should
not reconstruct quasi-inverses or expose a chosen equivalence datum.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- Inverse image on module sheaves along a ringed equivalence is an equivalence of
categories. -/
@[stacks 03DM "module pullback equivalence"]
theorem modulePullback_isEquivalence (f : Hom X Y)
    [f.modulePushforward.{z}.IsRightAdjoint] [f.IsRingedEquivalence] :
    f.modulePullback.{z}.IsEquivalence := sorry

/-- Direct image on module sheaves along a ringed equivalence is an equivalence of categories. -/
@[stacks 03DM "module pushforward equivalence"]
theorem modulePushforward_isEquivalence (f : Hom X Y) [f.IsRingedEquivalence] :
    f.modulePushforward.{z}.IsEquivalence := sorry

end RingedSite.Hom
