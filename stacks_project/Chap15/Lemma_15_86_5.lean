/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.CompleteIntersection
import StacksCheckRecall

/-!
# Lemma 15.86.5

@stack 0FV1
-/

@[expose] public section

open Algebra
open scoped TensorProduct

universe u

-- Source compatibility note: both tensor-factor algebra structures are needed to spell the
-- canonical pushout comparison; keeping them local avoids the known global instance diamond.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

/- Lemma 15.86.5 (0FV1): when both maps in the canonical cocartesian square are local complete
intersections, the kernel of the comparison on `H⁻¹` of the base-changed naive cotangent complex
of any presentation is finite projective over the pushout. -/
@[stacks 0FV1 "finite-projective kernel of H1 cotangent base change"]
#check fun {A A' B ι σ : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B]
    [RingHom.IsLocalCompleteIntersection (algebraMap A B)]
    [RingHom.IsLocalCompleteIntersection (algebraMap A' (A' ⊗[A] B))]
    (P : Presentation A B ι σ) =>
  (H1Cotangent.baseChangeComparison_ker_finiteProjective (A' := A') P :
    Module.FiniteProjective (A' ⊗[A] B)
      (LinearMap.ker (Presentation.naiveCotangentBaseChangeH1Comparison (R' := A') P)))

/- The kernel is taken on the presentation-level comparison map from Lemma 15.86.2. -/
#check fun {A A' B ι σ : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] (P : Presentation A B ι σ) =>
  (Presentation.naiveCotangentBaseChangeH1Comparison (R' := A') P :
    LinearMap.ker
        (LinearMap.baseChange (A' ⊗[A] B) P.toGenerators.toExtension.cotangentComplex) →ₗ[A' ⊗[A] B]
      (P.baseChange A').toGenerators.toExtension.H1Cotangent)

end
