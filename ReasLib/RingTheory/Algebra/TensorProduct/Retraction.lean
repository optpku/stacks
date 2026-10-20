/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Retraction Base Change of Product Decompositions

A split scalar tower `R → R' → R` cancels the iterated base change
`R ⊗[R'] (R' ⊗[R] S)`.  This leaf records the resulting transport of a
binary product decomposition as a reusable algebra equivalence.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x y

namespace Algebra.TensorProduct

/-- Base-changing a product decomposition through a split scalar tower yields
a product decomposition over the original base ring. -/
@[stacks 04GG "retraction base-change product equivalence"]
def baseChangeProdEquiv
    {R : Type u} {R' : Type v} {S : Type w} {A : Type x} {B : Type y}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R R'] [Algebra R S] [Algebra R' R] [Algebra R' A] [Algebra R' B]
    [IsScalarTower R R' R]
    (e : R' ⊗[R] S ≃ₐ[R'] A × B) :
    S ≃ₐ[R] (R ⊗[R'] A) × (R ⊗[R'] B) :=
  let eCancel : R ⊗[R'] (R' ⊗[R] S) ≃ₐ[R] S :=
    (Algebra.TensorProduct.cancelBaseChange R R' R R S).trans
      (Algebra.TensorProduct.lid R S)
  eCancel.symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).trans
      (Algebra.TensorProduct.prodRight R' R R A B)

end Algebra.TensorProduct
