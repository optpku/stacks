/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Complex.SmallRepresentative
public import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.PresheafOfModules.Cochain

/- Lemma 21.43.7 (0GYY): every representative contains a uniformly small subcomplex which is
still a representative of the same derived object. -/
@[stacks 0GYY]
#check @exists_small_representative_subcomplex

#check @derivedObjectCardinal
#check @derivedObjectCardinal_le_of_representation
#check @representationIsoOfSubcomplex
#check @representationIsoOfSubcomplex_hom
#check @derivedObjectCardinal_le_of_subcomplex

end CategoryTheory.PresheafOfModules.Cochain
