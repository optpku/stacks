/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Exact
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.9 (05NK): in a short exact sequence with flat quotient, the left term is flat if
and only if the middle term is flat. This single symmetric statement contains both clauses of the
source lemma. -/
@[stacks 05NK]
#check @SheafOfModules.RingedSite.flat_iff_flat_of_shortExact
