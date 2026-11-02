/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta

/-!
# Flat base change for the Berthelot-Ogus eta operator

Flat scalar extension preserves regular scalar actions degreewise.  Consequently it preserves the
termwise torsion-freeness needed by the eta construction, and the eta operator commutes with flat
base change on nonnegative cochain complexes.
@stack 0GSR
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings
open scoped BerthelotOgus nonZeroDivisors

universe u v w

namespace Module.Flat

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- A nonzerodivisor remains a nonzerodivisor after extension along a flat algebra.  This is the
ring-valued form of `Module.Flat.isSMulRegular_of_nonZeroDivisors`, transported along
`isSMulRegular_algebraMap_iff`. -/
@[stacks 0GSR "nonzerodivisors under flat base change"]
theorem algebraMap_mem_nonZeroDivisors [Flat A B] (f : A) (hf : f ∈ nonZeroDivisors A) :
    algebraMap A B f ∈ nonZeroDivisors B := by
  have h : IsSMulRegular B (algebraMap A B f) :=
    (isSMulRegular_algebraMap_iff B).mpr (isSMulRegular_of_nonZeroDivisors hf)
  exact mem_nonZeroDivisors_iff_left.mpr fun b hb ↦ h.right_eq_zero_of_smul hb

end Module.Flat

namespace CochainComplex.BerthelotOgus.Nat

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private theorem restrictScalars_flat [Module.Flat A B] :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  Module.Flat.of_linearEquiv
    (show ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[A] B from
      { __ := AddEquiv.refl B
        map_smul' := fun a b ↦ (Algebra.smul_def (R := A) (A := B) a b).symm })

/-- Flat extension of scalars preserves termwise torsion-freeness of a nonnegative cochain
complex. -/
@[stacks 0GSR "termwise torsion-freeness under flat base change"]
theorem IsTermwiseTorsionFree.extendScalars [Module.Flat A B] {f : A}
    {K : CochainComplex (ModuleCat.{max v w} A) ℕ} (hK : IsTermwiseTorsionFree f K) :
    IsTermwiseTorsionFree (algebraMap A B f)
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) := by
  have hflat := restrictScalars_flat (A := A) (B := B)
  letI := (algebraMap A B).toAlgebra
  letI : Module.Flat A B := hflat
  intro n
  change IsSMulRegular (B ⊗[A] K.X n) (algebraMap A B f)
  exact (isSMulRegular_algebraMap_iff B).mpr ((hK n).lTensor B)

namespace BaseChange

/-- The ambient degree map from the scalar extension of an eta term to the scalar extension of
the original term.  It is scalar extension of the defining subtype inclusion. -/
noncomputable def inclusionLinear
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A (term f K n)) →ₗ[B]
      (ModuleCat.extendScalars (algebraMap A B)).obj (K.X n) :=
  ((ModuleCat.extendScalars (algebraMap A B)).map
    (ModuleCat.ofHom (term f K n).subtype)).hom

/-- The ambient scalar-extension map sends the scalar extension of an eta term into the eta term
of the scalar-extended complex. -/
theorem inclusion_mem (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ)
    (x : (ModuleCat.extendScalars (algebraMap A B)).obj
      (ModuleCat.of A (term f K n))) :
    inclusionLinear (B := B) f K n x ∈
      term (algebraMap A B f)
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) n := by
  letI := (algebraMap A B).toAlgebra
  revert x
  change ∀ x : B ⊗[A] term f K n,
    (∃ y : B ⊗[A] K.X n, (algebraMap A B f) ^ n • y =
      (term f K n).subtype.baseChange B x) ∧
    ∃ z : B ⊗[A] K.X (n + 1), (algebraMap A B f) ^ (n + 1) • z =
      (K.d n (n + 1)).hom.baseChange B ((term f K n).subtype.baseChange B x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  | tmul b x =>
      obtain ⟨y, hy⟩ := x.property.1
      obtain ⟨z, hz⟩ := x.property.2
      change (f ^ n) • y = x.1 at hy
      change (f ^ (n + 1)) • z = K.d n (n + 1) x.1 at hz
      refine ⟨⟨b ⊗ₜ[A] y, ?_⟩, ⟨b ⊗ₜ[A] z, ?_⟩⟩
      · change (algebraMap A B f) ^ n • (b ⊗ₜ[A] y) = b ⊗ₜ[A] x.1
        rw [← map_pow, ← hy, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rfl
      · change (algebraMap A B f) ^ (n + 1) • (b ⊗ₜ[A] z) =
          b ⊗ₜ[A] (K.d n (n + 1) x.1)
        rw [← map_pow, ← hz, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rfl
  | add x y hx hy =>
      obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hx
      obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩ := hy
      exact ⟨⟨x₁ + y₁, by simp [smul_add, hx₁, hy₁]⟩,
        ⟨x₂ + y₂, by simp [smul_add, hx₂, hy₂]⟩⟩

/-- The degree map from the scalar extension of `η[f] K` to `η[algebraMap A B f]` of the
scalar-extended complex. -/
noncomputable def termLinear
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A (term f K n)) →ₗ[B]
      term (algebraMap A B f)
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) n :=
  (inclusionLinear (B := B) f K n).codRestrict _ (inclusion_mem (B := B) f K n)

/-- The bundled degree map from the scalar extension of `η[f] K` to the eta term of the
scalar-extended complex. -/
noncomputable def termHom
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (η[f] K)).X n ⟶
      (η[algebraMap A B f]
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K)).X n :=
  ConcreteCategory.ofHom (C := ModuleCat B) (termLinear (B := B) f K n)

/-- The underlying linear map of the bundled degree comparison is `termLinear`. -/
@[simp]
theorem termHom_hom
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (termHom (B := B) f K n).hom = termLinear (B := B) f K n := rfl

/-- The degreewise flat-base-change maps commute with the eta differentials. -/
theorem termLinear_comm (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    termHom (B := B) f K i ≫
        (η[algebraMap A B f]
          (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K)).d i j =
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (η[f] K)).d i j ≫
        termHom (B := B) f K j := by
  obtain rfl : i + 1 = j := hij
  change termHom (B := B) f K i ≫
      (η[algebraMap A B f]
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K)).d i (i + 1) =
    (ModuleCat.extendScalars (algebraMap A B)).map ((η[f] K).d i (i + 1)) ≫
      termHom (B := B) f K (i + 1)
  rw [eta_d, eta_d]
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  apply Subtype.ext
  rfl

/-- The canonical map from the scalar extension of `η[f] K` to the eta complex of the
scalar-extended complex. -/
@[stacks 0GSR "Berthelot-Ogus eta flat-base-change comparison"]
noncomputable def comparison (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) :
    ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (η[f] K) ⟶
      η[algebraMap A B f]
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) where
  f n := termHom (B := B) f K n
  comm' i j hij := termLinear_comm (B := B) f K i j hij

/-- The component of the eta base-change comparison is the canonical degree comparison. -/
@[simp]
theorem comparison_f
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (comparison (B := B) f K).f n = termHom (B := B) f K n := rfl

private theorem quotient_baseChange_smul
    {M : Type*} [AddCommGroup M] [Module A M] (a : A) (y : B ⊗[A] M) :
    (LinearMap.range (LinearMap.lsmul A M a)).mkQ.baseChange B
      (algebraMap A B a • y) = 0 := by
  let p := LinearMap.range (LinearMap.lsmul A M a)
  have hq (z : M) : p.mkQ (a • z) = 0 :=
    (Submodule.Quotient.mk_eq_zero p).mpr ⟨z, rfl⟩
  rw [map_smul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b z =>
      change algebraMap A B a • (b ⊗ₜ[A] (p.mkQ z)) = 0
      rw [TensorProduct.smul_tmul', algebraMap_smul,
        TensorProduct.smul_tmul, ← p.mkQ.map_smul, hq, TensorProduct.tmul_zero]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- For a flat algebra, the canonical base-change comparison for the eta operator is an
isomorphism.  The inverse remains encapsulated by `IsIso`; no chosen inverse is part of this API. -/
@[stacks 0GSR "Berthelot-Ogus eta commutes with flat base change"]
instance comparisonIsIso [Module.Flat A B] (f : A)
    (K : CochainComplex (ModuleCat.{max v w} A) ℕ) :
    IsIso (comparison (B := B) f K) := by
  have hbij (n : ℕ) : Function.Bijective (termLinear (B := B) f K n) := by
    have hflat := restrictScalars_flat (A := A) (B := B)
    letI := (algebraMap A B).toAlgebra
    letI : Module.Flat A B := hflat
    constructor
    · intro x y h
      apply Module.Flat.lTensor_preserves_injective_linearMap (M := B)
        (term f K n).subtype (term f K n).injective_subtype
      exact congrArg Subtype.val h
    · let p := LinearMap.range (LinearMap.lsmul A (K.X n) (f ^ n))
      let q := LinearMap.range (LinearMap.lsmul A (K.X (n + 1)) (f ^ (n + 1)))
      let g := p.mkQ.prod (q.mkQ.comp (K.d n (n + 1)).hom)
      have hex : Function.Exact (term f K n).subtype g := by
        rw [LinearMap.exact_iff, LinearMap.ker_prod, LinearMap.ker_comp,
          Submodule.ker_mkQ, Submodule.ker_mkQ, Submodule.range_subtype]
        rfl
      have hexB := Module.Flat.lTensor_exact B hex
      have hgB : ∀ x : B ⊗[A] K.X n,
          TensorProduct.prodRight A B B (K.X n ⧸ p) (K.X (n + 1) ⧸ q)
            (g.lTensor B x) =
          (p.mkQ.baseChange B x,
            q.mkQ.baseChange B ((K.d n (n + 1)).hom.baseChange B x)) := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]; rfl
        | tmul b z => rfl
        | add x y hx hy => simp [hx, hy]
      rintro ⟨x, hx⟩
      have hz : g.lTensor B x = 0 := by
        apply (TensorProduct.prodRight A B B (K.X n ⧸ p) (K.X (n + 1) ⧸ q)).injective
        rw [map_zero, hgB]
        apply Prod.ext
        · obtain ⟨y, hy⟩ := hx.1
          change (algebraMap A B f) ^ n • y = x at hy
          change p.mkQ.baseChange B x = 0
          rw [← hy, ← map_pow]
          exact quotient_baseChange_smul (B := B) (M := K.X n) (f ^ n) y
        · obtain ⟨y, hy⟩ := hx.2
          change (algebraMap A B f) ^ (n + 1) • y =
            (K.d n (n + 1)).hom.baseChange B x at hy
          change q.mkQ.baseChange B ((K.d n (n + 1)).hom.baseChange B x) = 0
          rw [← hy, ← map_pow]
          exact quotient_baseChange_smul (B := B) (M := K.X (n + 1)) (f ^ (n + 1)) y
      obtain ⟨t, ht⟩ := (hexB x).mp hz
      exact ⟨t, Subtype.ext ht⟩
  haveI (n : ℕ) : IsIso ((comparison (B := B) f K).f n) := by
    change IsIso (termHom (B := B) f K n)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (hbij n)
  exact HomologicalComplex.Hom.isIso_of_components _

end BaseChange

end CochainComplex.BerthelotOgus.Nat
