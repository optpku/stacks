/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalUnits.BaseField

universe u

/- Proposition 33.28.5: Let `X` be a connected reduced scheme, locally of finite type over a
field `k`, with finitely many irreducible components. If the integral closure of `k` in the
global sections of `X` is `k`, or `X` has a `k`-rational point, or `X` is geometrically
integral, then its global units modulo scalar units form a finitely generated abelian group.
-/
@[stacks 04L7] #check
  (AlgebraicGeometry.SchemeOverField.GlobalUnits.moduleFinite_of_baseFieldCondition :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [ConnectedSpace X.left] [AlgebraicGeometry.IsReduced X.left]
      [AlgebraicGeometry.LocallyAlgebraic X] [Finite (irreducibleComponents X.left)],
      (AlgebraicGeometry.SchemeOverField.BaseField.GlobalSections.isIntegrallyClosed X ∨
        AlgebraicGeometry.SchemeOverField.BaseField.hasRationalPoint X ∨
        AlgebraicGeometry.GeometricallyIntegral X.hom) →
        Module.Finite ℤ (Additive (AlgebraicGeometry.Scheme.Hom.unitsQuotient X.hom)))
