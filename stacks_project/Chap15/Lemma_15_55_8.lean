module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Resolution

/-!
# Lemma 15.55.8: injective character-module targets

@stack 01DC

The construction and injectivity theorem are valid for arbitrary rings.  They are owned by
`CharacterModule.Resolution`; this file is the source-facing recall.
-/

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 15.55.8 (Stacks `01DC`): for `J(M) = CharacterModule (F (CharacterModule M))`,
the module `J(M)` is injective. -/
@[stacks 01DC "Lemma 15.55.8"]
#check fun (R : Type u) [Ring R] (M : ModuleCat.{max u v} R) ↦
  (CharacterModule.Resolution.injective R M :
    Module.Injective R (CharacterModule.Resolution.obj R M))

/- The same target is available as an injective categorical object. -/
#check @CharacterModule.Resolution.obj_injective
#check @CharacterModule.Resolution.functor_obj
