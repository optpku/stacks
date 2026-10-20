/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

namespace IsGoodTripleModification

/-- Restricting a good-triple modification to an affine divisor-complex chart is the blowup
in the chart's product center. -/
theorem instIsBlowupRestrictAffineChart {X X' : Scheme.{u}} {D : X.IdealSheafData}
    [IsEffectiveCartierDivisor D.subschemeι]
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X}
    [IsGoodTripleModification D M b] (C : DivisorComplexChart D M) :
    IsBlowup (b ∣_ C.U) C.productCenter :=
  isBlowup_restrict_affineChart D M b C

end IsGoodTripleModification

/- Lemma 38.43.6: an effective Cartier divisor and a perfect derived module admit a universal
good-triple modification; its restriction to every affine divisor-complex chart is the blowup
in the product center, and over every quasi-compact open it is admissible away from the
restricted divisor. -/
@[stacks 0GTY] #check (AlgebraicGeometry.Scheme.exists_isGoodTripleModification :
  (X : Scheme.{u}) → (D : X.IdealSheafData) →
    [IsEffectiveCartierDivisor D.subschemeι]
    → (M : RingedSpace.ModuleDerived X.toRingedSpace) →
    RingedSpace.ModuleDerived.IsPerfect M →
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), IsGoodTripleModification D M b)

/- The affine-chart clause of Lemma 38.43.6. -/
#check (AlgebraicGeometry.Scheme.IsGoodTripleModification.isBlowup_restrict_affineChart :
  {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
    [IsEffectiveCartierDivisor D.subschemeι]
    → (M : RingedSpace.ModuleDerived X.toRingedSpace) → (b : X' ⟶ X) →
    [IsGoodTripleModification D M b] → (C : DivisorComplexChart D M) →
    IsBlowup (b ∣_ C.U) C.productCenter)

/- The quasi-compact admissibility clause of Lemma 38.43.6. -/
#check (AlgebraicGeometry.Scheme.IsGoodTripleModification.isAdmissibleBlowup_restrict :
  {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
    [IsEffectiveCartierDivisor D.subschemeι]
    → (M : RingedSpace.ModuleDerived X.toRingedSpace) →
    RingedSpace.ModuleDerived.IsPerfect M → (b : X' ⟶ X) →
    [IsGoodTripleModification D M b] → (W : X.Opens) → [QuasiCompact W.ι] →
    IsAdmissibleBlowup (D.comap W.ι).openComplement (b ∣_ W))

end AlgebraicGeometry.Scheme
