/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Complex.SmallSubcomplex
public import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.PresheafOfModules.Cochain

/- Lemma 21.43.6 (0GYX): prescribed local sections are contained in a subcomplex whose
section cardinality is uniformly bounded by the maximum of a fixed cardinal and the seed
cardinality. -/
@[stacks 0GYX]
#check @exists_small_subcomplex

#check @sectionsCardinal
#check @SectionFamily.cardinal
#check @SectionFamily.IsContainedIn
#check @SectionFamily.IsContainedIn.mono
#check @subcomplexCardinal

end CategoryTheory.PresheafOfModules.Cochain
