module

public import ReasLib.CategoryTheory.Sites.Topos.Point.Action
public import StacksCheckRecall.CommandCrossRef

/-!
# Forgetful point of `G`-sets

This historical Chapter 7 support module is now a recall-only entry point.  The reusable action
site, its forgetful point, its left-regular generator, and its named right-translation action are
owned by `ReasLib.CategoryTheory.Sites.Topos.Point.Action`.
-/

@[expose] public section

@[stacks 00YF "(1)"] #check Action.forgetfulPoint
#check Action.forgetElementsBaseInitial
#check Action.forgetfulPoint_sheafFiberIso_leftRegular
#check Action.leftRegularOrbitHom
#check Action.leftRegularOrbitHom_comp
#check Action.leftRegularRightMul
#check Action.leftRegularRightMul_comp_orbit
#check Action.rightTranslationAction
