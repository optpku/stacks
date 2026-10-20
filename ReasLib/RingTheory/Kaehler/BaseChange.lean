/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-Extended Base Change for Kaehler Differentials

For a tower `R → S → A → T`, this file owns the canonical map

`T ⊗[S] Ω[S⁄R] → T ⊗[A] Ω[A⁄R]`.

It is obtained by extending `KaehlerDifferential.mapBaseChange R S A` to `T`
and cancelling the repeated scalar extension.  The construction is independent
of presentations, local rings, and first-order thickenings.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open TensorProduct
open TensorProduct.AlgebraTensorModule

universe u v w x

namespace KaehlerDifferential

/-- The tensor-extended Kähler base-change map attached to a tower
`R → S → A → T`. -/
@[stacks 04EF "tensor-extended Kaehler base-change map"]
noncomputable def tensorMapBaseChange
    (R : Type u) (S : Type v) (A : Type w) (T : Type x)
    [CommRing R] [CommRing S] [CommRing A] [CommRing T]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Algebra A T] [Algebra S T] [IsScalarTower S A T] :
    T ⊗[S] Ω[S⁄R] →ₗ[T] T ⊗[A] Ω[A⁄R] :=
  (mapBaseChange R S A).baseChange T ∘ₗ
    (cancelBaseChange S A T T Ω[S⁄R]).symm.toLinearMap

/-- Computation of `tensorMapBaseChange` on pure tensors. -/
@[simp]
theorem tensorMapBaseChange_tmul
    (R : Type u) (S : Type v) (A : Type w) (T : Type x)
    [CommRing R] [CommRing S] [CommRing A] [CommRing T]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Algebra A T] [Algebra S T] [IsScalarTower S A T]
    (t : T) (x : Ω[S⁄R]) :
    tensorMapBaseChange R S A T (t ⊗ₜ[S] x) =
      t ⊗ₜ[A] KaehlerDifferential.map R R S A x := by
  simp [tensorMapBaseChange]

/-- The tensor-extended base-change map commutes with the canonical maps to
the Kähler differentials of the final algebra in a compatible tower. -/
@[stacks 06S8]
theorem mapBaseChange_comp_tensorMapBaseChange
    (Λ : Type u) (B : Type v) (A : Type w) (k : Type x)
    [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
    [Algebra Λ B] [Algebra Λ A] [Algebra Λ k]
    [Algebra B A] [Algebra B k] [Algebra A k]
    [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k] :
    mapBaseChange Λ A k ∘ₗ tensorMapBaseChange Λ B A k = mapBaseChange Λ B k := sorry

end KaehlerDifferential
