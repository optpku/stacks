module

public import ReasLib.RingTheory.Algebra.IsEpi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-square criteria for algebra epimorphisms

@stack 04VN

This leaf collects equivalent formulations of `Algebra.IsEpi R S` in terms of the two canonical
maps `S →ₐ[R] S ⊗[R] S` and tensor-square multiplication. It is independent of fibers,
localization, and finiteness hypotheses.
-/

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

namespace Algebra.IsEpi

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]

/- The pointwise tensor relation is Mathlib's canonical root criterion. -/

/-- An `R`-algebra is epic exactly when its two canonical maps to its tensor square agree. -/
@[stacks 04VN "canonical maps"]
theorem iff_includeLeft_eq_includeRight :
    Algebra.IsEpi R S ↔
      (includeLeft : S →ₐ[R] S ⊗[R] S) = (includeRight : S →ₐ[R] S ⊗[R] S) := sorry

/-- An `R`-algebra is epic exactly when tensor-square multiplication is bijective. -/
@[stacks 04VN "multiplication"]
theorem iff_bijective_lmul :
    Algebra.IsEpi R S ↔
      Function.Bijective (lmul' R : S ⊗[R] S →ₐ[R] S) := sorry

/-- An `R`-algebra is epic exactly when the left canonical map to its tensor square is
bijective. -/
@[stacks 04VN "left canonical map"]
theorem iff_bijective_includeLeft :
    Algebra.IsEpi R S ↔
      Function.Bijective (includeLeft : S →ₐ[R] S ⊗[R] S) := sorry

/-- Lemma 10.107.1 (Stacks `04VN`): epimorphy, equality of the two canonical tensor-square maps,
bijectivity of a canonical map, and bijectivity of tensor-square multiplication are equivalent. -/
@[stacks 04VN]
theorem tensorSquare_tfae :
    List.TFAE
      [ Algebra.IsEpi R S
      , (includeLeft : S →ₐ[R] S ⊗[R] S) = (includeRight : S →ₐ[R] S ⊗[R] S)
      , Function.Bijective (includeLeft : S →ₐ[R] S ⊗[R] S)
      , Function.Bijective (lmul' R : S ⊗[R] S →ₐ[R] S) ] := sorry

end Algebra.IsEpi
