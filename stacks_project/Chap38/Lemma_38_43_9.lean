/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.FiniteFreeLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.43.9: a good-triple modification is an isomorphism over the maximal open on
which all cohomology sheaves of the perfect derived module are finite locally free. -/
@[stacks 0F8W] #check (AlgebraicGeometry.Scheme.IsGoodTripleModification.isIsoRestrictFiniteFreeOpen :
    ∀ {X X' : Scheme.{u}} (D : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι]
      (M : RingedSpace.ModuleDerived X.toRingedSpace)
      (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b],
      IsIso (b ∣_ hM.finiteFreeOpen (fun x ↦ inferInstance)))
