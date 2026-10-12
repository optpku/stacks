/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat
import StacksCheckRecall

/-!
# Lemma 18.28.2

Objectwise module flatness is a reusable sufficient criterion for categorical flatness of a
module presheaf.
-/

@[expose] public section

/- Lemma 18.28.2 (03ES): a presheaf whose section modules are flat is flat. -/
@[stacks 03ES]
#check @PresheafOfModules.isFlat_of_flat_obj
