/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.FirstOrder.Unramified
import StacksCheckRecall

/-!
# Universal First-Order Thickenings and Kaehler Differentials

The Kähler comparison map is owned at the level of an arbitrary algebra tower;
universality is used only for the two conclusions of the source lemma.

@stack 04EF
-/

@[expose] public section

@[stacks 04EF "canonical Kaehler comparison map"]
#check @KaehlerDifferential.tensorMapBaseChange

@[stacks 04EF "comparison map on pure tensors"]
#check @KaehlerDifferential.tensorMapBaseChange_tmul

@[stacks 04EF "(1), formal unramifiedness of the thickening"]
#check @Algebra.Extension.FirstOrder.IsUniversal.formallyUnramified

@[stacks 04EF "(2), bijective Kaehler comparison"]
#check @Algebra.Extension.FirstOrder.IsUniversal.tensorMapBaseChange_bijective
