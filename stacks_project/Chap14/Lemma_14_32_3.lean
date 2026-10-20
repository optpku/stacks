/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration.CechNerve
import StacksCheckRecall

/-!
@stack 01AB

# Lemma 14.32.3 compatibility facade

The reusable theorem is owned by the boundary-inclusion morphism property `I.rlp` and uses the
canonical augmented Cech nerve of an arrow.
-/

@[expose] public section

open CategoryTheory
open SSet.modelCategoryQuillen

universe u

/- Lemma 14.32.3: the augmented Cech nerve of a surjective map is a trivial Kan fibration. -/
@[stacks 01AB]
#check (I.rlp.augmentedCechNerve.of_surjective :
  ∀ {A B : Type u} (f : A → B), Function.Surjective f →
    I.rlp ((Arrow.mk (TypeCat.ofHom f)).augmentedCechNerve.hom))

#check (I.rlp.augmentedCechNerve.of_epi :
  ∀ {A B : Type u} (f : A ⟶ B) [Epi f],
    I.rlp ((Arrow.mk f).augmentedCechNerve.hom))
