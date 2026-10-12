/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Unramified.Diagonal
import StacksCheckRecall

/-! @stack 02FL -/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.FormallyUnramified

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Unramified R S]

/- Lemma 10.151.4: for an unramified ring map, tensor multiplication is
localization away from an idempotent cutting out the diagonal. -/
@[stacks 02FL]
#check (Diagonal.isIdempotentLocalization R S :
  (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom.IsIdempotentLocalization)

#check (Diagonal.elem_isIdempotent R S :
  IsIdempotentElem (Algebra.FormallyUnramified.elem R S))

#check (Diagonal.ker_eq_span_one_sub R S :
  RingHom.ker (Algebra.TensorProduct.lmul' R).toRingHom =
    Ideal.span {1 - Algebra.FormallyUnramified.elem R S})

end Algebra.FormallyUnramified

#check @exists_idempotent_tensorProduct_self_isLocalization_of_unramified
