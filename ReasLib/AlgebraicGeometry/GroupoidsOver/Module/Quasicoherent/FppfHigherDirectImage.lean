/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.FppfSerreQuotient

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- The inclusion of quasi-coherent modules into fppf `LQCoh^{fbc}`. -/
def toFppfLQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ FppfModules.LQCohFbc X :=
  (FppfModules.lqcohFbc X).lift (QCoh.inclusion X) (QCoh.toLQCohFbc_mapsTo X)

/-- The underlying fppf module of `toFppfLQCohFbc` is `QCoh.inclusion`. -/
theorem toFppfLQCohFbc_comp_inclusion (X : GroupoidsOver S)
    [AlgebraicStack X] :
    toFppfLQCohFbc X ⋙ FppfModules.inclusion X = QCoh.inclusion X :=
  rfl

/-- Right-derived pushforward of a quasi-coherent fppf module remains in
fppf `LQCoh^{fbc}`. -/
theorem higherDirectImage_mem_lqcohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    FppfModules.lqcohFbc Y
      ((QCoh.inclusion X ⋙
          (fppfModulePushforward f).rightDerived i).obj F) := sorry

/-- Lift of ordinary fppf `R^i f_*` of a quasi-coherent module into fppf
`LQCoh^{fbc}`. -/
def higherDirectImageToLQCohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh X ⥤ FppfModules.LQCohFbc Y :=
  (FppfModules.lqcohFbc Y).lift
    (QCoh.inclusion X ⋙
      (fppfModulePushforward f).rightDerived i)
    (QCoh.higherDirectImage_mem_lqcohFbc f i)

/-- The underlying fppf module of `QCoh.higherDirectImageToLQCohFbc` is ordinary
`R^i f_*`. -/
theorem higherDirectImageToLQCohFbc_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.higherDirectImageToLQCohFbc f i ⋙ FppfModules.inclusion Y =
      QCoh.inclusion X ⋙
        (fppfModulePushforward f).rightDerived i :=
  rfl

/-- Applying the fppf quasi-coherent coreflector to higher direct image recovers
quasi-coherent higher direct image. -/
theorem higherDirectImageToLQCohFbc_comp_coreflector {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    higherDirectImageToLQCohFbc f i ⋙ FppfModules.LQCohFbc.coreflector Y =
      higherDirectImageFunctor f i := sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
