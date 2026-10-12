/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.IsEpi.TensorSquare
import StacksCheckRecall

/-!
# Epimorphisms and tensor squares

@stack 04VN
-/

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]

/- Lemma 10.107.1 (Stacks `04VN`): epimorphy, equality of the canonical tensor-square maps,
bijectivity of a canonical map, and bijectivity of tensor-square multiplication are equivalent. -/
@[stacks 04VN]
#check (Algebra.IsEpi.tensorSquare_tfae (R := R) (S := S) :
  List.TFAE
    [ Algebra.IsEpi R S
    , (includeLeft : S →ₐ[R] S ⊗[R] S) = (includeRight : S →ₐ[R] S ⊗[R] S)
    , Function.Bijective (includeLeft : S →ₐ[R] S ⊗[R] S)
    , Function.Bijective (lmul' R : S ⊗[R] S →ₐ[R] S) ])

end
