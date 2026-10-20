/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Square

/-!
# Equation 15.6.3.1

@stack 08KI

The source equation is represented by the canonical module-category pullback functor
`ModuleCat.extendScalarsToPullback`, built from the canonical commuting square
`ModuleCat.extendScalarsCommSq`.
-/

open CategoryTheory

@[stacks 08KI "canonical commuting-square data"]
#check @ModuleCat.extendScalarsCommSq

@[stacks 08KI "15.6.3.1 canonical functor"]
#check @ModuleCat.extendScalarsToPullback
