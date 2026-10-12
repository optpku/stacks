/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Contraction
public import ReasLib.RingTheory.Finiteness.Projective
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-Hom contraction for finite projective modules

The canonical comparison map is defined by Mathlib.  This leaf owns the reusable
finite-projective upgrade, while the finite-free equivalence remains in
`Mathlib.LinearAlgebra.Contraction`.

@stack 0DVB
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace TensorProduct

section

variable {R : Type u} [CommSemiring R]
variable {L : Type v} [AddCommMonoid L] [Module R L]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type x} [AddCommMonoid N] [Module R N]

/- The comparison is controlled only by the source module `M`; no finiteness
   hypothesis on the target or tensor factor is part of the canonical API. -/

/-- The tensor-Hom comparison is bijective when its source module is finite projective. -/
@[stacks 0DVB "finite-projective tensor-Hom comparison"]
theorem rTensorHomToHomRTensor_bijective
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (rTensorHomToHomRTensor (.id R) M N L) := sorry

end

end TensorProduct

namespace Module.FiniteProjective

section

variable {R : Type u} [CommSemiring R]
variable {L : Type v} [AddCommMonoid L] [Module R L]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type x} [AddCommMonoid N] [Module R N]

/-- The same comparison, accepting a finite-projective proposition as explicit evidence. -/
@[stacks 0DVB "explicit finite-projective evidence for tensor-Hom comparison"]
theorem rTensorHomToHomRTensor_bijective (hM : Module.FiniteProjective R M) :
    Function.Bijective (TensorProduct.rTensorHomToHomRTensor (.id R) M N L) := sorry

end

end Module.FiniteProjective
