/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalUnits.Basic

universe u

/-
Lemma 33.28.2: let `k` be an algebraically closed field and `X` an integral
scheme locally of finite type over `k`. Then the group of global units of `X`
modulo the scalar units from `k` is a finitely generated abelian group.
-/
@[stacks 04L5] #check
  (AlgebraicGeometry.SchemeOverField.GlobalUnits.instModuleFiniteOfIntegralLocallyAlgebraic :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsAlgClosed k]
      [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.LocallyAlgebraic X],
      Module.Finite ℤ
        (Additive (AlgebraicGeometry.Scheme.Hom.unitsQuotient X.hom)))
