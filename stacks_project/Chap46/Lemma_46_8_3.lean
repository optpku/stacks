/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Copresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]

/- Lemma 46.8.3 (1): the character dual of any `R`-module is pure injective. -/
@[stacks 0700]
#check
  (CharacterModule.moduleObj_pureInjective :
    ∀ (M : ModuleCat.{v} R),
      (CharacterModule.moduleObj R M).PureInjective)

/- Lemma 46.8.3 (2): an `R`-module is pure injective if and only if its canonical
map to the double character dual splits. -/
@[stacks 0700]
#check
  (ModuleCat.pureInjective_iff_isSplitMono_evaluationApp :
    ∀ (I : ModuleCat.{v} R),
      I.PureInjective ↔ IsSplitMono (CharacterModule.evaluationApp R I))

/- Lemma 46.8.3 (3): every `R`-module embeds into a pure injective module as the
first map of a universally exact short complex. -/
@[stacks 0700]
#check
  (ModuleCat.exists_universallyExact_pureInjective_copresentation :
    ∀ (M : ModuleCat.{v} R),
      ∃ (I N : ModuleCat.{v} R) (f : M ⟶ I) (g : I ⟶ N)
        (hzero : f ≫ g = 0),
        (ShortComplex.mk f g hzero).UniversallyExact ∧ I.PureInjective)
