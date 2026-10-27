/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.MapObstruction

/-! # Kernel and obstruction compatibility interface -/

@[expose] public section

open CategoryTheory AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

/-- The derived-category quotient on complexes of modules over a ringed space. -/
abbrev moduleQ (X : RingedSpace.{u}) :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules := DerivedCategory.Q

variable {X X' : RingedSpace.{u}} (h : X ⟶ X') [IsFirstOrderThickening h]

#check (conormalToTargetModule h :
  conormalSheaf h ⟶ (inverseImage_isSquareZero h).targetModule
    (inferInstance : IsIso (KernelIdeal.quotientComparison (inverseImageStructureSheafHomComm h))))

#check (targetModuleToIdealModule h :
  (inverseImage_isSquareZero h).targetModule
    (inferInstance : IsIso (KernelIdeal.quotientComparison (inverseImageStructureSheafHomComm h))) ⟶
    idealModule h)

#check (idealModuleToTargetModule h :
  idealModule h ⟶ (inverseImage_isSquareZero h).targetModule
    (inferInstance : IsIso (KernelIdeal.quotientComparison (inverseImageStructureSheafHomComm h))))

#check (kernelIdealPushforwardIso h : kernelIdealSheaf h ≅ (h _*).obj (idealModule h))

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

#check (mapObstruction :
  ∀ D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s',
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X1).obj (naiveCotangent f1)),
      (moduleQ X2).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))))

end AlgebraicGeometry.RingedSpace.Thickening
