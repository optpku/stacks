/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.GeometricallyNormal.FieldTests
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.165.1

@stack 037Z
-/

/- Lemma 10.165.1 (Stacks tag `037Z`): the field-extension test families for
geometric normality are owned by the shared geometric-normality leaf. -/
@[stacks 037Z]
#check @Algebra.IsGeometricallyNormal.fieldTensorTests_tfae

@[stacks 037Z "finite purely inseparable tensor test"]
#check @Algebra.IsGeometricallyNormal.iff_forall_isNormalRing_tensorProduct_finitePurelyInseparable

@[stacks 037Z "essentially finite-type tensor test"]
#check @Algebra.IsGeometricallyNormal.iff_forall_isNormalRing_tensorProduct_essFiniteType

@[stacks 037Z "perfect-closure tensor test"]
#check @Algebra.IsGeometricallyNormal.iff_isNormalRing_tensorProduct_perfectClosure
