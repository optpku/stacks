/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant.Finite
import StacksCheckRecall

/-!
# Finiteness of constant module sheaves

The source's nonempty-topos assumption is represented intrinsically by
`GrothendieckTopology.HasNonemptySheafTopos`; the constant module sheaf is
viewed through the canonical `SheafOfModules` functor in ReasLib.
-/

@[expose] public section

/- Lemma 18.42.5 (093N), finite-type clause. -/
@[stacks 093N "(1)"]
#check (@CategoryTheory.Sheaf.constant_isFiniteType_iff)

/- Lemma 18.42.5 (093N), finite-presentation clause. -/
@[stacks 093N "(2)"]
#check (@CategoryTheory.Sheaf.constant_isFinitePresentation_iff)

/- The reusable bridge and intrinsic site hypothesis. -/
#check (@CategoryTheory.Sheaf.ConstantModule.sheafFunctor)
#check (@CategoryTheory.GrothendieckTopology.HasNonemptySheafTopos)
