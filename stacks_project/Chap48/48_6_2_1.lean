module

public import ReasLib.CategoryTheory.Functor.DualityBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {D_Y D_X D_Y' D_X' D_R : Type u}
variable [Category.{v} D_Y] [Category.{v} D_X] [Category.{v} D_Y']
variable [Category.{v} D_X'] [Category.{v} D_R]
variable (gPull : D_Y ⥤ D_Y') (gPrimePull : D_X ⥤ D_X')
variable (a : D_Y ⥤ D_X) (aPrime : D_Y' ⥤ D_X')
variable (rHom : D_X'ᵒᵖ ⥤ D_X' ⥤ D_R) (M : D_X) (K : D_Y)
variable (baseChange : gPrimePull.obj (a.obj K) ⟶ aPrime.obj (gPull.obj K))

/- 48.6.2.1: applying `RHom` in its second variable to the base-change morphism
`L(g')^*a(K) ⟶ a'(Lg^*K)` gives the displayed morphism
`RHom (L(g')^*M) (L(g')^*a(K)) ⟶ RHom (L(g')^*M) (a'(Lg^*K))`. -/
@[stacks 0E45] #check
  (CategoryTheory.Functor.DualityBaseChange.rHomMap
    gPull gPrimePull a aPrime rHom M K baseChange :
    (rHom.obj (Opposite.op (gPrimePull.obj M))).obj (gPrimePull.obj (a.obj K)) ⟶
      (rHom.obj (Opposite.op (gPrimePull.obj M))).obj (aPrime.obj (gPull.obj K)))
