/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 21.10.1 (Tag 03F6): an injective abelian sheaf remains injective after
forgetting to the category of abelian presheaves.  The reusable owner is the
`PreservesInjectiveObjects` instance for `sheafToPresheaf`. -/
@[stacks 03F6 "sheaf-to-presheaf preservation of injectives"]
#check @CategoryTheory.Sheaf.sheafToPresheaf_preservesInjectiveObjects

/- Lemma 21.10.1 (Tag 03F6), objectwise form. -/
@[stacks 03F6 "injective abelian sheaf as a presheaf"]
#check @CategoryTheory.Sheaf.injective_toPresheaf

/- The objectwise statement is the specialization of the generic functor API. -/
#check @CategoryTheory.Functor.injective_obj_of_injective
