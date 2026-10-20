/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/- Definition 72.6.7: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `f ∈ (RationalFunction X)ˣ`. The principal Weil
divisor associated to `f` is the Weil divisor
`principalWeilDivisor X f : WeilDivisor X`, the locally finite sum of coefficients
`Z.ord f` over prime divisors `Z`. This is well defined by Lemma 72.6.6. -/
@[stacks 0ENP] #check (AlgebraicGeometry.AlgebraicSpace.principalWeilDivisor X : (RationalFunction X)ˣ → WeilDivisor X)
