/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.CommDiagram

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace

universe u

/-! The shared owner of the first-order-thickening commutative diagram. -/
#check (AlgebraicGeometry.RingedSpace.Thickening.CommDiagram.mk :
  {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}} →
    {i2 : X2 ⟶ X'2} → {f2 : X2 ⟶ S2} → {f'2 : X'2 ⟶ S'2} → {t2 : S2 ⟶ S'2} →
    {i1 : X1 ⟶ X'1} → {f1 : X1 ⟶ S1} → {f'1 : X'1 ⟶ S'1} → {t1 : S1 ⟶ S'1} →
    {g : X2 ⟶ X1} → {s : S2 ⟶ S1} → {s' : S'2 ⟶ S'1} →
    [IsFirstOrderThickening i2] → [IsFirstOrderThickening t2] →
    [IsFirstOrderThickening i1] → [IsFirstOrderThickening t1] →
    i2 ≫ f'2 = f2 ≫ t2 → i1 ≫ f'1 = f1 ≫ t1 →
    f2 ≫ s = g ≫ f1 → t2 ≫ s' = s ≫ t1 →
    AlgebraicGeometry.RingedSpace.Thickening.CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
