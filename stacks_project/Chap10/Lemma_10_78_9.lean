module

public import ReasLib.LinearAlgebra.TensorProduct.Contraction
import StacksCheckRecall

/-!
# Lemma 10.78.9

The tensor-Hom comparison for a finite projective source module is owned by
`TensorProduct.rTensorHomToHomRTensor_bijective`. This file records its exact
source specialization without introducing a compatibility alias.

@stack 0DVB
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {L : Type v} [AddCommGroup L] [Module R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Projective R M]

/- Lemma 10.78.9, tag `0DVB`: for a finite projective module `M`, the canonical map
`Hom_R(M, N) ⊗[R] L → Hom_R(M, N ⊗[R] L)` is bijective. -/
@[stacks 0DVB]
#check (TensorProduct.rTensorHomToHomRTensor_bijective :
  Function.Bijective (TensorProduct.rTensorHomToHomRTensor (.id R) M N L))

end


#check @TensorProduct.rTensorHomToHomRTensor_bijective
#check @Module.FiniteProjective.rTensorHomToHomRTensor_bijective
