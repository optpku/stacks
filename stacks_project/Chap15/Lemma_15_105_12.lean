module

import StacksCheckRecall
public import ReasLib.RingTheory.Unramified.TensorSquare

@[expose] public section

/-!
# Lemma 15.105.12

@stack 092M
-/

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

/- Lemma 15.105.12 (092M): flatness of the tensor-square multiplication map forces
the relative Kähler differentials to be trivial.  The reusable owner is the
canonical `Algebra.FormallyUnramified` statement in `ReasLib`; the source-facing
conclusion is recovered through its defining field. -/

@[stacks 092M "Lemma 15.105.12"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) ↦
  (Algebra.FormallyUnramified.of_tensorSquareMul_flat
      (A := A) (B := B) hflatMul).subsingleton_kaehlerDifferential

#check @Algebra.FormallyUnramified.of_tensorSquareMul_flat
