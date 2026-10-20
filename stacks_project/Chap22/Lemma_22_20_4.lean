/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Resolution
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (M : DifferentialGradedModule.{u, v} A)

/- Lemma 22.20.4 (09KP): every right DG module admits a quasi-isomorphic property P
resolution. -/
@[stacks 09KP] #check
  (DifferentialGradedModule.PropertyP.Resolution.nonempty A M :
    Nonempty (DifferentialGradedModule.PropertyP.Resolution A M))
