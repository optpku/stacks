/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DifferentialGradedBimodule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
variable {N : DifferentialGradedBimodule.{u, v, v, w} A B}
variable (hN : HasLeftPropertyP A B N)

/- Lemma 22.33.4 (0GZ2): a differential graded `(A, B)`-bimodule which has property P as a
left differential graded `A`-module computes its derived tensor product without replacement. -/
@[stacks 0GZ2] #check
  (Tensor.derivedCounit_isIso_of_hasLeftPropertyP hN :
    IsIso (Tensor.derivedCounit N))

#check @HasLeftPropertyP
#check @Tensor.derivedSourceFunctor_isInvertedBy_of_hasLeftPropertyP
#check @Tensor.computesAt_of_hasLeftPropertyP
#check @Tensor.derivedCounit_app_isIso_of_hasLeftPropertyP
