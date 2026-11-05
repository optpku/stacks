/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.MittagLeffler.Properties

@[expose] public section

/-!
# Tensor-Product Characterization of Mittag-Leffler Modules

This leaf owns the characterization of Mittag-Leffler modules by injectivity
of tensor products against arbitrary products of modules.

@stack 059M
@stack 05CN
@stack 05CT
-/

open scoped TensorProduct

universe u v w x

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Proposition 10.89.5, tag `059M`: a module is Mittag-Leffler exactly when tensoring it with
an arbitrary product injects into the product of the corresponding tensor products.

For the converse, the index and carrier universes must contain the ring universe: the proof
uses representatives of finitely presented `R`-modules and their tensor-kernel elements.
No lower bound from the universe of `M` is needed. The forward implication at arbitrary
test universes is available as `piRightHom_injective`. -/
@[stacks 059M]
theorem iff_piRightHom_injective :
    Module.MittagLeffler R M ↔
      ∀ (A : Type (max u w)) (Q : A → Type (max u x)) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
        Function.Injective (TensorProduct.piRightHom R R M Q) := sorry

/-- Tensoring a Mittag-Leffler module with a product injects into the product of tensors,
with no restriction on the universes of the index or the test modules. -/
theorem piRightHom_injective (hM : Module.MittagLeffler R M)
    (A : Type w) (Q : A → Type x) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    Function.Injective (TensorProduct.piRightHom R R M Q) := by
  let Q' : ULift.{u} A → Type (max u x) := fun a ↦ ULift.{u} (Q a.down)
  let e : (∀ a, Q a) ≃ₗ[R] (∀ a, Q' a) :=
    { toFun := fun q a ↦ ULift.up (q a.down)
      invFun := fun q a ↦ (q (ULift.up a)).down
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eT := TensorProduct.congr (LinearEquiv.refl R M) e
  have h := (iff_piRightHom_injective.{u, v, w, x} (R := R) (M := M)).mp hM
    (ULift.{u} A) Q'
  have hc (z : M ⊗[R] (∀ a, Q a)) (a : ULift.{u} A) :
      TensorProduct.piRightHom R R M Q' (eT z) a =
        TensorProduct.congr (LinearEquiv.refl R M)
          (ULift.moduleEquiv : ULift.{u} (Q a.down) ≃ₗ[R] Q a.down).symm
          (TensorProduct.piRightHom R R M Q z a.down) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m q => rfl
    | add z t hz ht => simp only [map_add, Pi.add_apply, hz, ht]
  intro s t hst
  apply eT.injective
  apply h
  funext a
  rw [hc, hc, hst]

/-- Lemma 10.88.9, tag `05CN`: the tensor product of two Mittag-Leffler
modules is Mittag-Leffler. -/
@[stacks 05CN]
theorem tensorProduct {N : Type w} [AddCommGroup N] [Module R N]
    (hM : Module.MittagLeffler R M) (hN : Module.MittagLeffler R N) :
    Module.MittagLeffler R (M ⊗[R] N) := sorry

end Module.MittagLeffler

namespace Module.MittagLeffler.RestrictScalars

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module R M]
variable [IsScalarTower R S M]

/-- Lemma 10.89.11: if `S` is Mittag-Leffler over `R`, while `M` is flat and
Mittag-Leffler over `S`, then `M` is Mittag-Leffler over `R`. -/
@[stacks 05CT]
theorem of_flat [MittagLeffler R S] [Module.Flat S M] [MittagLeffler S M] :
    MittagLeffler R M := sorry

end Module.MittagLeffler.RestrictScalars
