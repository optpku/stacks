/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DifferentialGradedCategory

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)
variable (P : Comp R (DifferentialGradedModule B))
variable {P' : Comp R (DifferentialGradedModule B)} (f : P ⟶ P')

/- Equation 22.31.0.1 (09LG): the internal-Hom DG functor represented by a differential graded
`(A, B)`-bimodule induces the displayed functor from right DG `B`-modules to right DG
`A`-modules. -/
@[stacks 09LG] #check
  ((DifferentialGradedBimodule.internalHomDgFunctor N).mapComp :
    Comp R (DifferentialGradedModule B) ⥤
      Comp R (DifferentialGradedModule A))

#check DifferentialGradedBimodule.internalHomDgFunctor_obj N P
#check (DifferentialGradedBimodule.internalHomDgFunctor N).mapComp.map f
