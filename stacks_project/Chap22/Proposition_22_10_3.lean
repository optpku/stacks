/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R] (A : CochainDGAlgebra.{u, w} R)

/- Proposition 22.10.3 (09KJ): the homotopy category of right differential graded
`A`-modules satisfies the octahedron axiom and is triangulated. -/
@[stacks 09KJ]
#check (inferInstance : IsTriangulated (K R (DifferentialGradedModule.{u, v} A)))
