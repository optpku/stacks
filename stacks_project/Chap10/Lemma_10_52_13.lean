module

public import ReasLib.RingTheory.LocalRing.Length.Fiber
import StacksCheckRecall

@[expose] public section

/-!
# Flat local base change and the closed fiber

Lemma 10.52.13 is retained as a source-facing recall of the reusable
closed-fiber length API.  The canonical quotient formula remains
`IsLocalRing.length_baseChange`; the ReasLib leaf gives the equivalent
`Ideal.Fiber (maximalIdeal A) B` self-length view used by the textbook.

@stack 02M1
-/

open IsLocalRing
open scoped TensorProduct

universe u v w

section Length

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
variable [AddCommGroup M] [Module A M]

/- Lemma 10.52.13 (1): for a flat local homomorphism `A ⟶ B`, the length of
`B ⊗[A] M` is the length of `M` times the self-length of the closed fiber. -/
@[stacks 02M1 "(1)"]
#check
  (IsLocalRing.length_baseChange_eq_mul_fiber (A := A) (B := B) (M := M) :
    Module.length B (B ⊗[A] M) =
      Module.length A M *
        Module.length (Ideal.Fiber (maximalIdeal A) B)
          (Ideal.Fiber (maximalIdeal A) B))

/- Lemma 10.52.13 (2): if the closed fiber has finite length over itself,
`M` has finite length over `A` exactly when `B ⊗[A] M` has finite length over `B`. -/
@[stacks 02M1 "(2)"]
#check
  (IsLocalRing.isFiniteLength_baseChange_iff (A := A) (B := B) (M := M) :
    IsFiniteLength (Ideal.Fiber (maximalIdeal A) B)
        (Ideal.Fiber (maximalIdeal A) B) →
      (IsFiniteLength A M ↔ IsFiniteLength B (B ⊗[A] M)))

end Length
