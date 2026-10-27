/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.DualityBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe vY vX vY' vX' vR uY uX uY' uX' uR

variable {D_Y : Type uY} {D_X : Type uX} {D_Y' : Type uY'}
variable {D_X' : Type uX'} {D_R : Type uR}
variable [Category.{vY} D_Y] [Category.{vX} D_X] [Category.{vY'} D_Y']
variable [Category.{vX'} D_X'] [Category.{vR} D_R]
variable (gPull : D_Y ⥤ D_Y') (gPrimePull : D_X ⥤ D_X')
variable (a : D_Y ⥤ D_X) (aPrime : D_Y' ⥤ D_X')
variable (rHom : D_X'ᵒᵖ ⥤ D_X' ⥤ D_R) (M : D_X) (K : D_Y)
variable (baseChange : gPrimePull.obj (a.obj K) ⟶ aPrime.obj (gPull.obj K))

/- 48.6.2.1: applying `RHom` in its second variable to the base-change morphism
`L(g')^*a(K) ⟶ a'(Lg^*K)` gives the displayed morphism
`RHom (L(g')^*M) (L(g')^*a(K)) ⟶ RHom (L(g')^*M) (a'(Lg^*K))`. -/
@[stacks 0E45] #check
  ((rHom.obj (Opposite.op (gPrimePull.obj M))).map baseChange :
    (rHom.obj (Opposite.op (gPrimePull.obj M))).obj (gPrimePull.obj (a.obj K)) ⟶
      (rHom.obj (Opposite.op (gPrimePull.obj M))).obj (aPrime.obj (gPull.obj K)))
