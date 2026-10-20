/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.CharacterModule
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 35.4.12: a module morphism is universally injective if and only if
its character-dual map is a split epimorphism. -/
@[stacks 08WU] #check
  (CharacterModule.universallyInjective_iff_isSplitEpi_dualMap :
    ∀ (R : Type u) [CommRing R] {M N : ModuleCat.{u} R} (f : M ⟶ N),
      LinearMap.UniversallyInjective.{u, u, u, u} f.hom ↔
        IsSplitEpi (CharacterModule.dualMap R f))
