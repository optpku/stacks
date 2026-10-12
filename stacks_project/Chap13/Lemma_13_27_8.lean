/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Abelian.Injective.Dimension.Ext
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.27.8

Ext-vanishing criteria for injective dimension are owned by the canonical
`HasInjectiveDimensionLT` namespace.
-/

/- Lemma 13.27.8: uniform vanishing of degree-`p` Ext groups gives injective
dimension strictly less than `p` for every target object. -/
@[stacks 0EWW] #check @CategoryTheory.HasInjectiveDimensionLT.of_uniform_ext

/- Companion check: the fixed-target form can be reused independently. -/
@[stacks 0EWW] #check @CategoryTheory.HasInjectiveDimensionLT.of_ext_vanishing
