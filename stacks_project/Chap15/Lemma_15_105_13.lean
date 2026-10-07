module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.TensorSquare

/-!
# Lemma 15.105.13

@stack 0CKP
-/

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

/- Lemma 15.105.13 (1): a finite-type algebra whose tensor-square multiplication
map is flat is unramified. -/
@[stacks 0CKP "Lemma 15.105.13 (1)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) ↦
  Algebra.Unramified.of_tensorSquareMul_flat (A := A) (B := B) hflatMul

/- Lemma 15.105.13 (2): a flat finitely presented algebra whose tensor-square
multiplication map is flat is etale. -/
@[stacks 0CKP "Lemma 15.105.13 (2)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] [Module.Flat A B]
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) ↦
  Algebra.Etale.of_tensorSquareMul_flat (A := A) (B := B) hflatMul

/- Lemma 15.105.13 (3): a finitely presented weakly etale algebra is etale. -/
@[stacks 0CKP "Lemma 15.105.13 (3)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] [Algebra.FinitePresentation A B] ↦
  Algebra.WeaklyEtale.etale_of_finitePresentation (A := A) (B := B)
