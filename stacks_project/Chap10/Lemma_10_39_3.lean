/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimit.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-!
# Flatness of filtered colimits

@stack 05UT

The reusable owner is stated for filtered categorical diagrams and arbitrary colimit cocones;
the second check exposes the corresponding canonical colimit instance.
-/

/- Lemma 10.39.3 (Tag 05UT), filtered colimit cocone. -/
@[stacks 05UT]
#check @ModuleCat.FilteredColimits.flat_of_isColimit

/- Lemma 10.39.3 (Tag 05UT), canonical filtered colimit. -/
@[stacks 05UT]
#check @ModuleCat.FilteredColimits.flatColimit
