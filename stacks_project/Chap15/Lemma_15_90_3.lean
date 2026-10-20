/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.BaseChange
public import ReasLib.Algebra.Module.IdealPower.BaseChange
import StacksCheckRecall

/-!
# Lemma 15.90.3 (05EC)

The three clauses are the primary-component comparison, the Hom comparison,
and the equivalence on ideal-power torsion modules.

@stack 05EC
-/

@[expose] public section

#check @Ideal.primaryComponent.baseChangeUnit

/- Lemma 15.90.3 (1): flat base change along an isomorphism modulo `I`
identifies the source and target primary components. -/
@[stacks 05EC "Lemma 15.90.3 (1): primary-component comparison"]
#check @Ideal.primaryComponent.baseChangeUnit_bijective

/- Lemma 15.90.3 (2): extension of scalars induces a bijection on Hom sets
when either module is ideal-power torsion. -/
@[stacks 05EC "Lemma 15.90.3 (2): Hom comparison"]
#check @ModuleCat.IdealPower.BaseChange.homMap_bijective

/- Lemma 15.90.3 (3): extension of scalars is an equivalence on the full
subcategories of ideal-power torsion modules. -/
@[stacks 05EC "Lemma 15.90.3 (3): torsion-category equivalence"]
#check @ModuleCat.IdealPower.BaseChange.restricted_isEquivalence
