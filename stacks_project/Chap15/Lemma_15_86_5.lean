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
intersections, the kernel of the `H⁻¹` naive-cotangent comparison is finite projective over the
pushout. -/
@[stacks 0FV1 "finite-projective kernel of H1 cotangent base change"]
#check fun {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B]
    [RingHom.IsLocalCompleteIntersection (algebraMap A B)]
    [RingHom.IsLocalCompleteIntersection (algebraMap A' (A' ⊗[A] B))] =>
  (H1Cotangent.baseChangeComparison_ker_finiteProjective (A := A) (A' := A') (B := B) :
    Module.FiniteProjective (A' ⊗[A] B)
      (LinearMap.ker (H1Cotangent.baseChangeComparison (R := A) (R' := A') (S := B))))

/- The kernel is taken on the canonical comparison map from Lemma 15.86.2. -/
#check fun {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] =>
  (H1Cotangent.baseChangeComparison (R := A) (R' := A') (S := B) :
    A' ⊗[A] B ⊗[B] H1Cotangent A B →ₗ[A' ⊗[A] B]
      H1Cotangent A' (A' ⊗[A] B))

end
