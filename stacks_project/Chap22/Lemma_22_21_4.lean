/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Resolution
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (M : DifferentialGradedModule.{u, v} A)

/- Lemma 22.21.4 (09KU): every right DG `A`-module admits a quasi-isomorphism to a right DG
`A`-module with a specified property `(I)` filtration. -/
@[stacks 09KU] #check
  (DifferentialGradedModule.PropertyI.Resolution.nonempty A M :
    Nonempty (DifferentialGradedModule.PropertyI.Resolution A M))
