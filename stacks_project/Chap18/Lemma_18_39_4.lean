/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 18.39.4: module pullback preserves a short exact sequence whose quotient is flat. -/
@[stacks 0G6R]
#check @RingedSite.Hom.map_shortExact_of_flat_X₃
