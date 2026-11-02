/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.HopkinsLevitzki
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

/-!
# Residue-field modules on annihilated kernels of Artinian local algebra morphisms
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The kernel of a morphism in `ArtinianLocalAlgCat` annihilated by `m_{A'}`. -/
abbrev kerModule {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) : Type u :=
  RingHom.ker f.hom.toRingHom

private theorem kerModule_out_residue (A' : ArtinianLocalAlgCat Λ k) (c : k) :
    A'.residueFieldIso
      (IsLocalRing.residue A'.carrier (Quotient.out (A'.residueFieldIso.symm c))) = c := by
  change A'.residueFieldIso (Quotient.mk _ (Quotient.out _)) = c
  rw [Quotient.out_eq, AlgEquiv.apply_symm_apply]

private theorem kerModule_out_mul_eq {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (c : k) (r : A'.carrier)
    (hr : A'.residueFieldIso (IsLocalRing.residue A'.carrier r) = c)
    (i : kerModule f h_ann) :
    Quotient.out (A'.residueFieldIso.symm c) * i.1 = r * i.1 := by
  have hres : IsLocalRing.residue A'.carrier
      (Quotient.out (A'.residueFieldIso.symm c)) = IsLocalRing.residue A'.carrier r := by
    apply A'.residueFieldIso.injective
    rw [kerModule_out_residue, hr]
  have hmem := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hres
  have hz : (Quotient.out (A'.residueFieldIso.symm c) - r) * i.1 ∈
      (⊥ : Ideal A'.carrier) := by
    rw [← h_ann]
    exact Ideal.mul_mem_mul hmem i.property
  apply sub_eq_zero.mp
  rw [← sub_mul]
  exact Ideal.mem_bot.mp hz

/-- The residue identification of `A'` makes `ker f` into a `k`-module, using that
`m_{A'}` annihilates the kernel. -/
noncomputable instance instModule_kerModule {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    Module k (kerModule f h_ann) where
  smul c x :=
    ⟨Quotient.out (A'.residueFieldIso.symm c) * x.1, Ideal.mul_mem_left _ _ x.property⟩
  one_smul i := by
    apply Subtype.ext
    change Quotient.out (A'.residueFieldIso.symm 1) * i.1 = i.1
    rw [kerModule_out_mul_eq f h_ann 1 1 (by simp) i, one_mul]
  mul_smul c d i := by
    apply Subtype.ext
    change Quotient.out (A'.residueFieldIso.symm (c * d)) * i.1 =
      Quotient.out (A'.residueFieldIso.symm c) *
        (Quotient.out (A'.residueFieldIso.symm d) * i.1)
    rw [kerModule_out_mul_eq f h_ann (c * d)
      (Quotient.out (A'.residueFieldIso.symm c) *
        Quotient.out (A'.residueFieldIso.symm d))
      (by simp only [map_mul, kerModule_out_residue]) i, mul_assoc]
  smul_zero c := by
    apply Subtype.ext
    change Quotient.out (A'.residueFieldIso.symm c) * 0 = 0
    exact mul_zero _
  smul_add c i j := by
    apply Subtype.ext
    change Quotient.out (A'.residueFieldIso.symm c) * (i.1 + j.1) =
      Quotient.out (A'.residueFieldIso.symm c) * i.1 +
        Quotient.out (A'.residueFieldIso.symm c) * j.1
    exact mul_add _ _ _
  add_smul c d i := by
    apply Subtype.ext
    change Quotient.out (A'.residueFieldIso.symm (c + d)) * i.1 =
      Quotient.out (A'.residueFieldIso.symm c) * i.1 +
        Quotient.out (A'.residueFieldIso.symm d) * i.1
    rw [kerModule_out_mul_eq f h_ann (c + d)
      (Quotient.out (A'.residueFieldIso.symm c) +
        Quotient.out (A'.residueFieldIso.symm d))
      (by simp only [map_add, kerModule_out_residue]) i, add_mul]
  zero_smul i := by
    apply Subtype.ext
    change Quotient.out (A'.residueFieldIso.symm 0) * i.1 = 0
    rw [kerModule_out_mul_eq f h_ann 0 0 (by simp) i, zero_mul]

/-- The kernel of a morphism of Artinian local algebras annihilated by the maximal ideal is
a finite module over the residue field. -/
instance instModuleFinite_kerModule {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    Module.Finite k (kerModule f h_ann) := by
  letI : IsScalarTower A'.carrier k (kerModule f h_ann) :=
    IsScalarTower.of_algebraMap_smul fun r i =>
      Subtype.ext (kerModule_out_mul_eq f h_ann (algebraMap A'.carrier k r) r rfl i)
  exact Module.Finite.of_restrictScalars_finite A'.carrier k (kerModule f h_ann)

/-- Multiplication by any representative of a residue scalar computes its action on an
annihilated kernel. -/
theorem kerModule_smul_eq {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (c : k) (r : A'.carrier) (hr : A'.residueFieldIso (IsLocalRing.residue A'.carrier r) = c)
    (i : kerModule f h_ann) :
    (c • i).1 = r * i.1 :=
  kerModule_out_mul_eq f h_ann c r hr i

end ArtinianLocalAlgCat
