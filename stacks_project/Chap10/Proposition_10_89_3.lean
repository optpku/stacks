/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Pi.FinitePresentation

/-!
# Finitely presented modules and products

@stack 059K
-/

@[expose] public section

/- Proposition 10.89.3 is owned by the reusable tensor-product API. -/

@[stacks 059K]
#check @Module.FinitePresentation.tfae_piRightHom_bijective
