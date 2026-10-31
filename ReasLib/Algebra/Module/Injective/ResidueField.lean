/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

universe u v w

/-- A power-torsion module over a local ring embeds into a finite product of copies of
an injective hull of the residue field when its maximal-ideal socle has finite dimension. -/
theorem Module.exists_injective_to_pi_of_isIdealPowerTorsion
    (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    [AddCommGroup M] [Module R M]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull)
    (hM : Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal R) M) (n : ℕ)
    (hsocle : Nonempty
      ((IsLocalRing.maximalIdeal R).powerAnnihilatedSubmodule M 1 ≃ₗ[R]
        (Fin n → IsLocalRing.ResidueField R))) :
    ∃ f : M →ₗ[R] (Fin n → E), Function.Injective f := sorry

/-- The maximal-ideal torsion submodule of a module over a local ring is a module over
the residue field. -/
instance Submodule.instModuleResidueFieldTorsionByMaximalIdeal
    (R : Type u) (M : Type w) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] :
    Module (IsLocalRing.ResidueField R)
      (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R)) :=
  inferInstanceAs <| Module (R ⧸ IsLocalRing.maximalIdeal R)
    (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R))

noncomputable section

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The residue field acts on the space of linear maps from the residue field to the ring
by precomposition with multiplication on the domain. -/
instance instModuleResidueFieldLinearMapResidueFieldSelf :
    Module (ResidueField A) (ResidueField A →ₗ[A] A) where
  smul c f :=
    { toFun := fun x ↦ f (c * x)
      map_add' := by
        intro x y
        simp only [mul_add]
        exact f.map_add _ _
      map_smul' := by
        intro a x
        rw [show c * (a • x) = a • (c * x) by
          simp [Algebra.smul_def, mul_comm, mul_assoc]]
        exact f.map_smul a (c * x) }
  one_smul := by
    intro f
    ext x
    change f (1 * x) = f x
    rw [one_mul]
  mul_smul := by
    intro c d f
    ext x
    change f ((c * d) * x) = f (d * (c * x))
    congr 1
    ac_rfl
  smul_zero := by
    intro c
    ext x
    change (0 : ResidueField A →ₗ[A] A) (c * x) = 0
    rfl
  smul_add := by
    intro c f g
    ext x
    change (f + g) (c * x) = f (c * x) + g (c * x)
    rfl
  add_smul := by
    intro c d f
    ext x
    change f ((c + d) * x) = f (c * x) + f (d * x)
    rw [add_mul, map_add]
  zero_smul := by
    intro f
    ext x
    change f (0 * x) = 0
    rw [zero_mul, map_zero]

/-- Scalar multiplication on the residue-field dual evaluates by precomposition with
multiplication: `(c • f) x = f (c * x)`. -/
theorem smul_linearMap_residueField_self_apply
    (c : ResidueField A) (f : ResidueField A →ₗ[A] A) (x : ResidueField A) :
    (c • f) x = f (c * x) := rfl

/-- The residue-field dual of a self-injective Artinian local ring is finite-dimensional
over its residue field. -/
instance instFiniteDimensionalLinearMapResidueFieldSelf
    [IsArtinianRing A] [Module.Injective A A] :
    FiniteDimensional (ResidueField A) (ResidueField A →ₗ[A] A) := by
  letI : IsScalarTower A (ResidueField A) (ResidueField A →ₗ[A] A) :=
    ⟨fun a c f ↦ by
      ext x
      change f ((a • c) * x) = a • f (c * x)
      rw [smul_mul_assoc, map_smul]⟩
  haveI : Module.Finite A (ResidueField A →ₗ[A] A) := inferInstance
  exact Module.Finite.of_restrictScalars_finite A (ResidueField A) _

/-- The residue-field dual of a self-injective Artinian local ring has dimension one
over its residue field. -/
theorem finrank_linearMap_residueField_self_eq_one
    [IsArtinianRing A] [Module.Injective A A] :
    Module.finrank (ResidueField A) (ResidueField A →ₗ[A] A) = 1 := by
  obtain ⟨I, hI⟩ := IsAtomic.exists_atom (α := Submodule A A)
  haveI : IsSimpleModule A I := isSimpleModule_iff_isAtom.mpr hI
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule A I)
  have hm' : m = maximalIdeal A := eq_maximalIdeal hm
  subst m
  let f : ResidueField A →ₗ[A] A := I.subtype.comp e.symm.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hf0 : f ≠ 0 := by
    intro h
    have h01 : (0 : ResidueField A) = 1 := hf (by simp [h])
    exact zero_ne_one h01
  apply finrank_eq_one f hf0
  intro g
  obtain ⟨h, hh⟩ := Module.Injective.extension_property A A _ _ f hf g
  refine ⟨residue A (h 1), ?_⟩
  ext x
  rw [smul_linearMap_residueField_self_apply]
  calc
    f (residue A (h 1) * x) = (h 1) • f x := by
      rw [← ResidueField.algebraMap_eq, ← Algebra.smul_def, map_smul]
    _ = h (f x) := by
      have heq := h.map_smul (f x) (1 : A)
      simp only [smul_eq_mul, mul_one] at heq
      rw [heq, smul_eq_mul, mul_comm]
    _ = g x := DFunLike.congr_fun hh x

end IsLocalRing
