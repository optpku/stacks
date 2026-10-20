/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.TensorProduct.Domination
public import ReasLib.LinearAlgebra.UniversallyInjective

/-!
# Base change of tensor-kernel domination

This file owns the compatibility between tensor-kernel domination and extension of scalars.
Preservation is formal; reflection uses universal injectivity of the scalar map.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

namespace TensorProduct.AlgebraTensorModule

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M : Type w} {N : Type x} {Q : Type y}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid Q] [Module R Q]

/-- Distribution of base change over tensor products is natural in the first module. -/
@[stacks 059B "base-change naturality"]
theorem rTensor_comp_distribBaseChange (f : M →ₗ[R] N) :
    ((f.baseChange S).rTensor (S ⊗[R] Q)).comp
        (distribBaseChange R S M Q).toLinearMap =
      (distribBaseChange R S N Q).toLinearMap.comp
        ((f.rTensor Q).baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s mq
  induction mq using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul m q => simp

end TensorProduct.AlgebraTensorModule

namespace LinearMap.Dominates

section Preserve

variable {R : Type u} [CommSemiring R]
variable {P N Q : Type (max u v w)}
variable [AddCommMonoid P] [Module R P]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid Q] [Module R Q]

/-- Extension of scalars preserves tensor-kernel domination. -/
@[stacks 059B "base change"]
theorem baseChange {f : P →ₗ[R] N} {g : P →ₗ[R] Q}
    (hdom : g.Dominates f) (S : Type v) [CommSemiring S] [Algebra R S] :
    (g.baseChange S).Dominates (f.baseChange S) := by
  intro T _ _
  letI : Module R T := Module.compHom T (algebraMap R S)
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eP : (S ⊗[R] P) ⊗[S] T ≃ₗ[R] P ⊗[R] T :=
    (TensorProduct.comm S (S ⊗[R] P) T).restrictScalars R ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S T P).restrictScalars R ≪≫ₗ
        TensorProduct.comm R T P
  let eN : (S ⊗[R] N) ⊗[S] T ≃ₗ[R] N ⊗[R] T :=
    (TensorProduct.comm S (S ⊗[R] N) T).restrictScalars R ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S T N).restrictScalars R ≪≫ₗ
        TensorProduct.comm R T N
  let eQ : (S ⊗[R] Q) ⊗[S] T ≃ₗ[R] Q ⊗[R] T :=
    (TensorProduct.comm S (S ⊗[R] Q) T).restrictScalars R ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S T Q).restrictScalars R ≪≫ₗ
        TensorProduct.comm R T Q
  have hf : eN.toLinearMap.comp (((f.baseChange S).rTensor T).restrictScalars R) =
      (f.rTensor T).comp eP.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul sp t =>
      induction sp using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul s p => simp [eP, eN]
  have hg : eQ.toLinearMap.comp (((g.baseChange S).rTensor T).restrictScalars R) =
      (g.rTensor T).comp eP.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul sp t =>
      induction sp using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul s p => simp [eP, eQ]
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  have hfz : f.rTensor T (eP z) = 0 := by
    calc
      f.rTensor T (eP z) = eN ((f.baseChange S).rTensor T z) :=
        (LinearMap.congr_fun hf z).symm
      _ = eN 0 := by rw [hz]
      _ = 0 := map_zero eN
  have hgz := LinearMap.mem_ker.mp (hdom T (LinearMap.mem_ker.mpr hfz))
  apply eQ.injective
  calc
    eQ ((g.baseChange S).rTensor T z) = g.rTensor T (eP z) := LinearMap.congr_fun hg z
    _ = 0 := hgz
    _ = eQ 0 := by simp

end Preserve

section Reflect

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {P N Q : Type (max u v w)}
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup Q] [Module R Q]

/-- Universally injective scalar extension reflects tensor-kernel domination. -/
@[stacks 05A5 "domination reflection"]
theorem of_baseChange {f : P →ₗ[R] N} {g : P →ₗ[R] Q}
    (hdom : (g.baseChange S).Dominates (f.baseChange S))
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w}
      (Algebra.linearMap R S)) :
    g.Dominates f := by
  intro T _ _
  let dP := TensorProduct.AlgebraTensorModule.distribBaseChange R S P T
  let dN := TensorProduct.AlgebraTensorModule.distribBaseChange R S N T
  let dQ := TensorProduct.AlgebraTensorModule.distribBaseChange R S Q T
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  have hfz : (f.rTensor T).baseChange S (1 ⊗ₜ[R] z) = 0 := by
    simp [hz]
  have hfdz : (f.baseChange S).rTensor (S ⊗[R] T) (dP (1 ⊗ₜ[R] z)) = 0 := by
    calc
      (f.baseChange S).rTensor (S ⊗[R] T) (dP (1 ⊗ₜ[R] z)) =
          dN ((f.rTensor T).baseChange S (1 ⊗ₜ[R] z)) :=
        LinearMap.congr_fun
          (TensorProduct.AlgebraTensorModule.rTensor_comp_distribBaseChange f) _
      _ = 0 := by rw [hfz]; simp
  have hgdz := LinearMap.mem_ker.mp
    (hdom (S ⊗[R] T) (LinearMap.mem_ker.mpr hfdz))
  have hgz : (g.rTensor T).baseChange S (1 ⊗ₜ[R] z) = 0 := by
    apply dQ.injective
    calc
      dQ ((g.rTensor T).baseChange S (1 ⊗ₜ[R] z)) =
          (g.baseChange S).rTensor (S ⊗[R] T) (dP (1 ⊗ₜ[R] z)) :=
        (LinearMap.congr_fun
          (TensorProduct.AlgebraTensorModule.rTensor_comp_distribBaseChange g) _).symm
      _ = 0 := hgdz
      _ = dQ 0 := by simp
  apply (TensorProduct.lid R (Q ⊗[R] T)).symm.injective
  apply hRS.rTensor_injective (Q ⊗[R] T)
  simpa using hgz

/-- Universally injective scalar extension preserves and reflects tensor-kernel domination. -/
@[stacks 05A5 "domination base change"]
theorem iff_baseChange (f : P →ₗ[R] N) (g : P →ₗ[R] Q)
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w}
      (Algebra.linearMap R S)) :
    g.Dominates f ↔ (g.baseChange S).Dominates (f.baseChange S) :=
  ⟨fun h ↦ h.baseChange S, fun h ↦ h.of_baseChange hRS⟩

end Reflect

end LinearMap.Dominates
