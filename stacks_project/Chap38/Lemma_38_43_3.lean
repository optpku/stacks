/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived.Perfect

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived

universe u

/- Lemma 38.43.3: if an effective Cartier divisor, a perfect derived module, and the
ambient scheme form a good triple, then derived ideal-sheaf eta of the module is perfect. -/
@[stacks 0GTW] #check
  (AlgebraicGeometry.Scheme.IsGoodTriple.etaIsPerfect :
    ∀ {X : Scheme.{u}} (D : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι]
      (M : RingedSpace.ModuleDerived X.toRingedSpace)
      (hM : RingedSpace.ModuleDerived.IsPerfect M) (hgood : Scheme.IsGoodTriple D M),
      RingedSpace.ModuleDerived.IsPerfect ((functor D.toSubobject).obj M))
