/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Exact
import StacksCheckRecall

/-!
# Lemma 15.55.6: exactness of character duality

@stack 01DA

For an arbitrary ring the character dual is naturally a module over the opposite ring.  The
commutative endofunctor is retained below only as a specialization.
-/

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 15.55.6 (Stacks `01DA`): character duality is an exact contravariant functor from
left `R`-modules to left `Rᵐᵒᵖ`-modules. -/
@[stacks 01DA "exactness of character duality over a ring"]
#check fun (R : Type u) [Ring R] ↦
  (CharacterModule.opExact R :
    exactFunctor (ModuleCat.{v} R)ᵒᵖ (ModuleCat.{v} Rᵐᵒᵖ)
      (CharacterModule.opFunctor R))

/- Exactness already exists at the underlying additive-group level. -/
#check @CharacterModule.exact_dual

/- For a commutative ring, duality is an exact contravariant endofunctor. -/
#check fun (R : Type u) [CommRing R] ↦
  (CharacterModule.exact R :
    exactFunctor (ModuleCat.{v} R)ᵒᵖ (ModuleCat.{v} R)
      (CharacterModule.functor R))
