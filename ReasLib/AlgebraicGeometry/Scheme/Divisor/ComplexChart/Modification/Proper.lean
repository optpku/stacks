/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- An effective Cartier divisor and a perfect derived module admit a proper universal
modification on which their pullbacks form a good triple. -/
theorem existsProperGoodTripleModification (X : Scheme.{u}) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsGoodTripleModification D M b ∧ IsProper b := sorry

namespace IsGoodTripleModification

/-- A good-triple modification is canonically an isomorphism over the complement of the
divisor. -/
instance instIsIsoRestrictOpenComplement {X X' : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X}
    [IsGoodTripleModification D M b] : IsIso (b ∣_ D.openComplement) := sorry

end IsGoodTripleModification

end AlgebraicGeometry.Scheme
