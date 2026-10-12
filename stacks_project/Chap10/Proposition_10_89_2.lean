/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Pi.FinitePresentation

/-!
# Finite modules and products

@stack 059J
-/

@[expose] public section

/- Proposition 10.89.2 is owned by the reusable tensor-product API. -/

@[stacks 059J]
#check @Module.Finite.tfae_piRightHom_surjective
