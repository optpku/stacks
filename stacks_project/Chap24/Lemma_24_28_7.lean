/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DifferentialGradedCategory

noncomputable section

universe u v

namespace DifferentialGradedBimodule.Tensor.Derived

variable {R : Type u} [CommRing R]
variable {A B C : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule.{u, v} A B)
variable (N' : DifferentialGradedBimodule.{u, v} B C)
variable (h : IsIso (ordinaryComparison N N'))

/-
Lemma 24.28.7 (tag 0FTL): invertibility of the canonical derived-to-ordinary relative tensor
comparison implies invertibility of the canonical comparison from successive derived tensor
functors to tensoring by the relative tensor bimodule.  The algebraic DG owner exposes the
ordinary comparison, the natural transformation, its factorization, and the resulting
isomorphism separately.  The ringed-site specialization remains to be built.
-/
#check (ordinaryComparison N N')
#check (comparison N N')
#check (comparison_fac N N')
@[stacks 0FTL "composition comparison for derived tensor functors"]
#check (comparison_isIso N N' h : IsIso (comparison N N'))
#check
  (comparisonIso N N' (comparison_isIso N N' h) :
    derivedFunctor N ⋙ derivedFunctor N' ≅
      derivedFunctor (DifferentialGradedBimodule.Tensor.bimodule N N'))

end DifferentialGradedBimodule.Tensor.Derived
