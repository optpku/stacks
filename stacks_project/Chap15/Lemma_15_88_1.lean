/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.DerivedLimit
import StacksCheckRecall

/-!
# Lemma 15.88.1: derived inverse limits for sequential varying-ring modules

@stack 091D

The construction and its five independent clauses are owned by
`CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit`.  This file is the
source-facing recall and keeps the established unqualified names available to older Chapter 15
consumers.
-/

@[expose] public section

open CategoryTheory

export CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit
  (ringedModuleLimitTower ringedModuleInverseLimitFunctor
    ringedModuleDerivedInverseLimitFunctor)

namespace CategoryTheory

/- Textbook notation for the varying-ring derived inverse-limit object. -/
scoped notation:max "R" " lim(" K ")" =>
  Functor.obj
    (SequentialInverseSystem.ModuleSystem.DerivedLimit.ringedModuleDerivedInverseLimitFunctor
      _ _) K

end CategoryTheory

/- Lemma 15.88.1 (Stacks 091D): the inverse-limit functor on varying-ring module systems has a
total right derived functor. -/
@[stacks 091D] #check
  @CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit.ringedModuleDerivedInverseLimitFunctor

/- Lemma 15.88.1 (1): higher derived inverse limits vanish above degree `1`. -/
@[stacks 091D "(1)"] #check
  @CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit.homology_isZero_of_one_lt

/- Lemma 15.88.1 (2): the product-difference complex is expressed canonically by the Milnor
derived-limit presentation of the fixed-base tower. -/
@[stacks 091D "(2)"] #check
  @CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit.isDerivedLimit_of_object

/- Lemma 15.88.1 (3): Mittag-Leffler systems are right acyclic for inverse limit. -/
@[stacks 091D "(3)"] #check
  @CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit.rightAcyclic_of_isMittagLeffler

/- Lemma 15.88.1 (4): every derived object has a termwise inverse-limit-acyclic representative. -/
@[stacks 091D "(4)"] #check
  @CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit.exists_termwiseRightAcyclic_representative

/- Lemma 15.88.1 (5): a termwise acyclic complex computes the derived inverse limit. -/
@[stacks 091D "(5)"] #check
  @CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit.computes_of_termwiseRightAcyclic
