/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.RepresentedHom
import StacksCheckRecall

/-!
# Lemma 15.87.5

@stack 0919
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.87.5 (Stacks 0919): applying `Hom(L, -)` to a Milnor triangle gives the short exact
sequence from `R¹ lim Hom(L, K_n[-1])` to `lim Hom(L, K_n)`.  The neutral API is
`HomotopyLimit.IsOf.homShortExact`; this is the source-labelled recall. -/
@[stacks 0919]
#check @CategoryTheory.HomotopyLimit.IsOf.homShortExact

#check @CategoryTheory.HomotopyLimit.IsOf.homTower
#check @CategoryTheory.HomotopyLimit.IsOf.shiftedHomTower
