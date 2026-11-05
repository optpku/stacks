/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Strict
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Complex

/-!
# Ideal complexes and restriction for commuting thickening chains

Restriction needs no flatness. The canonical retraction needs only the top
first-order thickenings and their complex condition, not short exactness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

namespace ThickeningSquareChain

variable {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
variable {f : X ⟶ S} {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable {t1 : S ⟶ S1} {t2 : S ⟶ S2} {t3 : S ⟶ S3}

/-- Restrict any middle module along the middle inclusion. -/
noncomputable def moduleRestrict (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3)
    (M : X2.Modules) : X.Modules :=
  (i2 ^*).obj M

/-- The retraction supplied by the top ideal complex. -/
noncomputable def canonicalSplitting
    [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
    [IsFirstOrderThickening i3]
    (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3)
    (hC : IsComplex C.h C.k) : X1 ⟶ X :=
  canonicalTrivialization C.h C.k hC

/-- The top complex gives a left inverse without exactness or flatness. -/
theorem canonicalSplitting_leftInv
    [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
    [IsFirstOrderThickening i3]
    (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3)
    (hC : IsComplex C.h C.k) :
    i1 ≫ C.canonicalSplitting hC = 𝟙 X :=
  canonicalTrivialization_leftInv C.h C.k hC

end ThickeningSquareChain

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
