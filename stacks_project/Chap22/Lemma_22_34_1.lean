/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.Basic
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable {A B C : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)
variable (N' : DifferentialGradedBimodule B C)
variable (h_ordinary : IsIso
  (DifferentialGradedBimodule.Tensor.Derived.ordinaryComparison N N'))

/- Lemma 22.34.1: invertibility of the comparison at the right `B`-module underlying `N`
identifies successive derived tensoring with derived tensoring by `N ⊗_B N'`. -/
@[stacks 0BZ3] #check
  (DifferentialGradedBimodule.Tensor.Derived.comparison_isIso N N' h_ordinary :
    IsIso (DifferentialGradedBimodule.Tensor.Derived.comparison N N'))

#check @DifferentialGradedBimodule.Tensor.Derived.ordinaryComparison
#check @DifferentialGradedBimodule.Tensor.Derived.comparison
#check @DifferentialGradedBimodule.Tensor.Derived.comparisonIso
#check @DifferentialGradedBimodule.Tensor.bimodule
