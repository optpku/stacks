/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Presheaf.MonoEpi

import StacksCheckRecall

@[expose] public section

/-!
[stacks 00V7]

Lemma 7.3.2 is the objectwise injective/surjective characterization of isomorphisms of
set-valued presheaves.
-/

#check CategoryTheory.Presheaf.mono_iff_injective
#check CategoryTheory.Presheaf.epi_iff_surjective
@[stacks 00V7] #check CategoryTheory.Presheaf.isIso_iff_injective_and_surjective
