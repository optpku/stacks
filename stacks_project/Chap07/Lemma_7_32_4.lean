/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Functor.PresheafFiber
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 7.32.4 — Presheaf fiber/costalk adjunction

The generic construction is owned by `ReasLib.CategoryTheory.Functor.PresheafFiber`.
-/

open CategoryTheory

/- Lemma 7.32.4: for a set-valued functor `u`, the presheaf-valued costalk is right adjoint to
the presheaf fiber functor. -/
@[stacks 00Y7] #check @Functor.presheafFiberCostalkAdj

/- The corresponding right-adjoint instance is part of the same neutral API. -/
#check @Functor.presheafCostalk_isRightAdjoint
