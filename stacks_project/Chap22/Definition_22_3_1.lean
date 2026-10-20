/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra
import StacksCheckRecall

universe u v

variable (R : Type u) [CommRing R]

/- Definition 22.3.1 (1) (061V): a chain differential graded algebra is canonically
represented by `ChainDGAlgebra`. -/
@[stacks 061V] #check (ChainDGAlgebra.{u, v} R : Type _)

/- Definition 22.3.1 (2) (061V): the cochain convention is canonically represented by
`CochainDGAlgebra`. -/
@[stacks 061V] #check (CochainDGAlgebra.{u, v} R : Type _)
