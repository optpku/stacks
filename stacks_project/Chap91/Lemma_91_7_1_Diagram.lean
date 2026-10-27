/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.RelativeDiagram
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.FittingMap

/-! # Relative thickening diagram compatibility interface -/

@[expose] public section

open CategoryTheory AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

#check (RelativeDiagram.of :
  ∀ (comm : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (ν : idealModule i1 ⟶ (g _*).obj (idealModule i2)),
    KernelSquare comm ν → RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')

#check (FittingMap.spec :
  ∀ {D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s'} (φ : FittingMap D),
    i2 ≫ φ.hom = g ≫ i1 ∧ φ.hom ≫ f'1 = f'2 ≫ s' ∧
      kernelMapOf i1 g i2 inferInstance φ.hom φ.comm_top = D.ν)

end AlgebraicGeometry.RingedSpace.Thickening
