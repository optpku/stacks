/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DifferentialGradedBimodule

universe u v w x y

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}
variable (N : DifferentialGradedBimodule.{u, w, x, y} A B)

/- Lemma 22.33.1 (09LR): tensoring by a DG bimodule induces a triangulated functor on homotopy
categories. -/
@[stacks 09LR] #check
  (Tensor.mapK_isTriangulated N : (Tensor.dgFunctor N).mapK.IsTriangulated)

#check @Tensor.mapKCommShiftIso
