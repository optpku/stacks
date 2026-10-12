/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (x y : C) [HasBinaryBiproduct x y]

/- Lemma 12.3.10 (1): in the direct sum `x ⊞ y` with structure morphisms
`biprod.inl`, `biprod.inr`, `biprod.fst`, and `biprod.snd` as in Lemma `12.3.4`,
the inclusion `biprod.inl : x ⟶ x ⊞ y` is a kernel of the projection
`biprod.snd : x ⊞ y ⟶ y`. This is the canonical mathlib kernel-fork statement. -/
@[stacks 09QG] #check biprod.isKernelSndKernelFork

/- Lemma 12.3.10 (2): dually, in the same direct-sum decomposition, the projection
`biprod.fst : x ⊞ y ⟶ x` is a cokernel of the inclusion
`biprod.inr : y ⟶ x ⊞ y`. This is the canonical mathlib cokernel-cofork statement. -/
@[stacks 09QG] #check biprod.isCokernelInrCokernelFork

end

end CategoryTheory
