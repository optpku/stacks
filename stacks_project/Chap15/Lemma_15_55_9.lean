/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Resolution

/-!
# Lemma 15.55.9: functorial injective embeddings

@stack 01DD

The arrow functor and its functorial-injectives witness are valid over an arbitrary ring.  The
witness remains named rather than a second global instance, avoiding conflict with the canonical
Baer construction.
-/

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 15.55.9 (1): the canonical embeddings `M ⟶ J(M)` form a
functor to the arrow category. -/
@[stacks 01DD "Lemma 15.55.9 (1): arrow functor"]
#check fun (R : Type u) [Ring R] ↦
  (CharacterModule.Resolution.arrowFunctor R :
    ModuleCat.{max u v} R ⥤ Arrow (ModuleCat.{max u v} R))

/- Lemma 15.55.9 (2): the same explicit construction supplies functorial
injective embeddings. -/
@[stacks 01DD "Lemma 15.55.9 (2): functorial injectives"]
#check fun (R : Type u) [Ring R] ↦
  (CharacterModule.Resolution.functorialInjectives R :
    HasFunctorialInjectives (ModuleCat.{max u v} R))

/- The natural transformation itself remains available to consumers that
need its components rather than the packaged property. -/
#check @CharacterModule.Resolution.ι
#check @CharacterModule.Resolution.ιAppValue_freeMk
