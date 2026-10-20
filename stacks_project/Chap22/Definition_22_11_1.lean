/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite
import StacksCheckRecall

/-!
# Definition 22.11.1

The Koszul-twisted opposite construction is owned by
`ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite`.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/- Definition 22.11.1 (09JG): the opposite cochain differential graded algebra. -/
@[stacks 09JG]
#check (CochainDGAlgebra.opposite A : CochainDGAlgebra.{u, v} R)
