/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.FieldTheory.Separable.TensorSquare

@[expose] public section

/-!
# Lemma 15.105.15

@stack 092P
-/

open scoped TensorProduct

universe u v

/- Lemma 15.105.15, tag `092P`: the source writes the same map as
`Algebra.TensorProduct.lmul' K`; the shared owner uses the equivalent canonical
`Algebra.tensorSquareMultiplication K L` map-level interface. -/
@[stacks 092P "Lemma 15.105.15"]
#check fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hflat : (Algebra.tensorSquareMultiplication K L).Flat) ↦
  Algebra.IsSeparable.of_tensorSquareMul_flat (K := K) (L := L) hflat

#check fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hflat : (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).Flat) ↦
  Algebra.IsSeparable.of_tensorSquareMul_flat (K := K) (L := L) hflat

#check @Algebra.IsSeparable.of_tensorSquareMul_flat
