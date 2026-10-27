/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.MapObstruction
import Mathlib.CategoryTheory.Adjunction.Additive
import StacksCheckRecall

/-!
# Obstructions and compatible maps of first-order thickenings

The canonical Ext¹ class detects compatible fillings. When a filling exists, differences
between fillings are classified by Hom from relative differentials, with the pullback Hom
and degree-zero Ext identifications.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

/- Lemma 91.7.1. For the given commutative first-order cube and compatible kernel map,
the canonical obstruction in Ext¹ vanishes exactly when a compatible filling exists. -/
@[stacks 08U8] #check (AlgebraicGeometry.RingedSpace.Thickening.mapObstruction_eq_zero_iff :
  ∀ D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s',
    mapObstruction D = 0 ↔ Nonempty (FittingMap D))

#check (AlgebraicGeometry.RingedSpace.Thickening.fittingMap_principalHomogeneous :
  ∀ (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') (φ φ' : FittingMap D),
    ∃! α : Ω[f1] ⟶ (g _*).obj (idealModule i2), FittingMap.perturb α φ = φ')

#check (AlgebraicGeometry.RingedSpace.Thickening.homOmegaPushforwardEquiv :
  (Ω[f1] ⟶ (g _*).obj (idealModule i2)) ≃ ((g^*).obj Ω[f1] ⟶ idealModule i2))

#check (AlgebraicGeometry.RingedSpace.Thickening.homOmegaExtZero_bijective :
  Function.Bijective (fun α : Ω[f1] ⟶ (g _*).obj (idealModule i2) ↦ homOmegaExtZero α))

#check (((pullbackPushforwardAdjunction g).homAddEquiv Ω[f1] (idealModule i2)).symm :
  (Ω[f1] ⟶ (g _*).obj (idealModule i2)) ≃+ ((g^*).obj Ω[f1] ⟶ idealModule i2))

#check (AlgebraicGeometry.RingedSpace.Thickening.homOmegaExtZeroAddEquiv :
  (Ω[f1] ⟶ (g _*).obj (idealModule i2)) ≃+
    Ext⁽(0 : ℤ)⁾((modulePullbackDerived g).obj
      ((DerivedCategory.Q (C := X1.Modules)).obj (naiveCotangent f1)),
      (DerivedCategory.Q (C := X2.Modules)).obj
        ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))))

end AlgebraicGeometry.RingedSpace.Thickening
