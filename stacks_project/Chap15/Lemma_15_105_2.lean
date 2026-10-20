/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Weakly.Flat
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.105.2 (092C)

@stack 092C

For `A ⟶ B` and a `B`-module `N`, flatness of `B ⊗[A] B ⟶ B` together with `A`-flatness of `N`
implies `B`-flatness of `N`.  The map-level statement is owned by the shared weakly etale leaf.
-/

/- Lemma 15.105.2: tensor-square multiplication flatness transports module flatness. -/
@[stacks 092C "Lemma 15.105.2"]
#check @Module.Flat.of_flat_base_and_flat_tensorSquareMultiplication

/- Weakly etale specialization used by later weak-dimension arguments. -/
@[stacks 092C "weakly etale specialization"]
#check @Module.Flat.of_isWeaklyEtale
