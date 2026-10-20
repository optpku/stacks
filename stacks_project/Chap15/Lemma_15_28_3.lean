/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Functoriality
import StacksCheckRecall

/-!
# Functoriality of the Koszul differential graded algebra

@stack 0624
-/

@[expose] public section

/- Lemma 15.28.3: a compatible linear map induces a morphism of the corresponding
commutative Koszul differential graded algebras. -/
@[stacks 0624 "Lemma 15.28.3"]
#check @KoszulComplex.commMonMap

#check @KoszulComplex.map
#check @KoszulComplex.commMonMap_hom
#check @KoszulComplex.commMonMap_hom_f
