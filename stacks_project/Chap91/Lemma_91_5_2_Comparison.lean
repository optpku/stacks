/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealMul.Comparison

/-!
# Canonical maps `ℐ ⊗ F ⟶ ℐ F'` and `f^* 𝒥 ⊗ F ⟶ ℐ F'`

Along a first-order thickening, the kernel-ideal action on `F'` pulls back to an
`𝒪_X`-map `ℐ ⊗ F ⟶ ℐ F'`. A morphism of first-order thickenings then supplies the
canonical comparison `f^* 𝒥 ⊗ F ⟶ ℐ F'` by tensoring `sourceIdealMap` with `F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open scoped AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening.Hom

#check (AlgebraicGeometry.RingedSpace.Hom.actionToIdealMulRestrict :
  {X X' : RingedSpace.{u}} → (i : X ⟶ X') → [IsFirstOrderThickening i] →
    (F' : X'.Modules) → idealModule i ⊗ (i ^*).obj F' ⟶ idealMulRestrict i F')

#check (AlgebraicGeometry.RingedSpace.Hom.actionToIdealMulRestrict_comp :
  ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] (F' : X'.Modules),
    actionToIdealMulRestrict i F' =
      (Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) F').hom ≫
        (i ^*).map (actionToIdealMul i F'))

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.sourceIdealMulMap :
  {T U : Thickening.{u}} → [IsFirstOrderThickening T.hom] →
    [IsFirstOrderThickening U.hom] → (g : T ⟶ U) → (F' : T.right.Modules) →
      (g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj F' ⟶
        idealMulRestrict T.hom F')

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.sourceIdealMulMap_comp :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) (F' : T.right.Modules),
    sourceIdealMulMap g F' =
      tensorHom (sourceIdealMap g) (𝟙 ((T.hom^*).obj F')) ≫
        actionToIdealMulRestrict T.hom F')
