/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Module
import StacksCheckRecall

universe u v w

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/- Definition 22.4.1 (1) (09JI): right differential graded modules over a cochain
differential graded algebra are canonically represented by `DifferentialGradedModule`. -/
@[stacks 09JI] #check (DifferentialGradedModule.{u, w} A : Type _)

variable (M N : DifferentialGradedModule.{u, w} A)

/- Definition 22.4.1 (2) (09JI): their morphisms are canonically represented by
`DifferentialGradedModule.Hom`. -/
@[stacks 09JI] #check (DifferentialGradedModule.Hom M N : Type _)
