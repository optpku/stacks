/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.SectionMaps
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local and global comparison squares for associated tensor products

This module packages the degree-zero, standard-open, and stalk realizations of the canonical
associated-sheaf tensor morphism.  Every concrete linear map is assembled from named values and
linearity laws, so downstream users may reuse the individual layers without reconstructing
bundled maps or local instance environments.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe uA uσ

namespace AlgebraicGeometry.Proj.AssociatedModule.Tensor

open GradedModule.TensorProduct

variable {A : Type uA} {σ : Type uσ} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {M N : Type uA} [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ]

/-! ## Degree-zero tensor comparison -/

/-- A pure tensor of two degree-zero homogeneous elements belongs to degree zero of the total
tensor grading. -/
theorem degreeZeroValue_mem (m : ℳ 0) (n : ℵ 0) :
    (m : M) ⊗ₜ[A] (n : N) ∈ grading A ℳ ℵ 0 := sorry

/-- The degree-zero total-grading element represented by a pure tensor. -/
noncomputable def degreeZeroValue (m : ℳ 0) (n : ℵ 0) :
    grading A ℳ ℵ 0 :=
  ⟨(m : M) ⊗ₜ[A] (n : N), degreeZeroValue_mem ℳ ℵ m n⟩

/-- The degree-zero tensor value is additive in its second argument. -/
theorem degreeZeroValue_add_right (m : ℳ 0) (n₁ n₂ : ℵ 0) :
    degreeZeroValue (A := A) ℳ ℵ m (n₁ + n₂) =
      degreeZeroValue (A := A) ℳ ℵ m n₁ + degreeZeroValue (A := A) ℳ ℵ m n₂ := sorry

/-- The degree-zero tensor value is linear in its second argument. -/
theorem degreeZeroValue_smul_right (m : ℳ 0) (r : 𝒜 0) (n : ℵ 0) :
    degreeZeroValue (A := A) ℳ ℵ m (r • n) =
      r • degreeZeroValue (A := A) ℳ ℵ m n := sorry

/-- Fixing the first degree-zero factor gives a linear map in the second factor. -/
noncomputable def degreeZeroRight (m : ℳ 0) :
    ℵ 0 →ₗ[𝒜 0] grading A ℳ ℵ 0 where
  toFun := degreeZeroValue (A := A) ℳ ℵ m
  map_add' := degreeZeroValue_add_right (A := A) ℳ ℵ m
  map_smul' := degreeZeroValue_smul_right (A := A) 𝒜 ℳ ℵ m

/-- The degree-zero tensor value is additive in its first argument. -/
theorem degreeZeroValue_add_left (m₁ m₂ : ℳ 0) (n : ℵ 0) :
    degreeZeroValue (A := A) ℳ ℵ (m₁ + m₂) n =
      degreeZeroValue (A := A) ℳ ℵ m₁ n + degreeZeroValue (A := A) ℳ ℵ m₂ n := sorry

/-- The degree-zero tensor value is linear in its first argument. -/
theorem degreeZeroValue_smul_left (r : 𝒜 0) (m : ℳ 0) (n : ℵ 0) :
    degreeZeroValue (A := A) ℳ ℵ (r • m) n =
      r • degreeZeroValue (A := A) ℳ ℵ m n := sorry

/-- The right-input degree-zero tensor map is additive in its fixed first input. -/
theorem degreeZeroRight_add (m₁ m₂ : ℳ 0) :
    degreeZeroRight 𝒜 ℳ ℵ (m₁ + m₂) =
      degreeZeroRight 𝒜 ℳ ℵ m₁ + degreeZeroRight 𝒜 ℳ ℵ m₂ := sorry

/-- The right-input degree-zero tensor map is linear in its fixed first input. -/
theorem degreeZeroRight_smul (r : 𝒜 0) (m : ℳ 0) :
    degreeZeroRight 𝒜 ℳ ℵ (r • m) =
      r • degreeZeroRight 𝒜 ℳ ℵ m := sorry

/-- The bilinear map from two degree-zero pieces to degree zero of the total tensor grading. -/
noncomputable def degreeZeroPairing :
    ℳ 0 →ₗ[𝒜 0] ℵ 0 →ₗ[𝒜 0] grading A ℳ ℵ 0 where
  toFun := degreeZeroRight 𝒜 ℳ ℵ
  map_add' := degreeZeroRight_add 𝒜 ℳ ℵ
  map_smul' := degreeZeroRight_smul 𝒜 ℳ ℵ

/-- The canonical map from the tensor product of the two degree-zero pieces to degree zero in
the total tensor grading. -/
@[stacks 01MK "degree-zero tensor comparison"]
noncomputable def degreeZeroMap :
    ℳ 0 ⊗[𝒜 0] ℵ 0 →ₗ[𝒜 0] grading A ℳ ℵ 0 :=
  TensorProduct.lift (degreeZeroPairing 𝒜 ℳ ℵ)

/-- The degree-zero tensor map sends a pure tensor to its ambient pure tensor. -/
@[simp]
theorem degreeZeroMap_tmul (m : ℳ 0) (n : ℵ 0) :
    Subtype.val (degreeZeroMap 𝒜 ℳ ℵ (m ⊗ₜ[𝒜 0] n)) =
      (m : M) ⊗ₜ[A] (n : N) := sorry

/-- The degree-zero tensor map bundled as a morphism over the degree-zero ring. -/
noncomputable def degreeZeroHom :
    ModuleCat.of (𝒜 0) (ℳ 0 ⊗[𝒜 0] ℵ 0) ⟶
      ModuleCat.of (𝒜 0) (grading A ℳ ℵ 0) :=
  ModuleCat.ofHom (degreeZeroMap 𝒜 ℳ ℵ)

/-! ## Pure tensor sections induced by degree-zero elements -/

/-- The pure tensor section determined by two degree-zero homogeneous elements. -/
noncomputable def degreeZeroSectionValue (m : ℳ 0) (n : ℵ 0) :
    (ModuleCat.restrictScalars (AssociatedModule.degreeZeroRingHom 𝒜)).obj
      ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
        (AssociatedModule.sheaf 𝒜 ℵ)).val.obj (op ⊤)) :=
  tensorSectionLinear (AlgebraicGeometry.Proj 𝒜).sheaf
    (AssociatedModule.sheaf 𝒜 ℳ) (AssociatedModule.sheaf 𝒜 ℵ) (op ⊤)
      (AssociatedModule.degreeZeroSection 𝒜 ℳ m)
      (AssociatedModule.degreeZeroSection 𝒜 ℵ n)

/-- The degree-zero pure tensor section is additive in its second argument. -/
theorem degreeZeroSectionValue_add_right (m : ℳ 0) (n₁ n₂ : ℵ 0) :
    degreeZeroSectionValue 𝒜 ℳ ℵ m (n₁ + n₂) =
      degreeZeroSectionValue 𝒜 ℳ ℵ m n₁ +
        degreeZeroSectionValue 𝒜 ℳ ℵ m n₂ := sorry

/-- The degree-zero pure tensor section is linear in its second argument. -/
theorem degreeZeroSectionValue_smul_right (m : ℳ 0) (r : 𝒜 0) (n : ℵ 0) :
    degreeZeroSectionValue 𝒜 ℳ ℵ m (r • n) =
      r • degreeZeroSectionValue 𝒜 ℳ ℵ m n := sorry

/-- Fixing the first degree-zero element gives a linear pure-tensor section map. -/
noncomputable def degreeZeroSectionRight (m : ℳ 0) :
    ℵ 0 →ₗ[𝒜 0]
      (ModuleCat.restrictScalars (AssociatedModule.degreeZeroRingHom 𝒜)).obj
        ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
          (AssociatedModule.sheaf 𝒜 ℵ)).val.obj (op ⊤)) where
  toFun := degreeZeroSectionValue 𝒜 ℳ ℵ m
  map_add' := degreeZeroSectionValue_add_right 𝒜 ℳ ℵ m
  map_smul' := degreeZeroSectionValue_smul_right 𝒜 ℳ ℵ m

/-- The degree-zero pure tensor section is additive in its first argument. -/
theorem degreeZeroSectionValue_add_left (m₁ m₂ : ℳ 0) (n : ℵ 0) :
    degreeZeroSectionValue 𝒜 ℳ ℵ (m₁ + m₂) n =
      degreeZeroSectionValue 𝒜 ℳ ℵ m₁ n +
        degreeZeroSectionValue 𝒜 ℳ ℵ m₂ n := sorry

/-- The degree-zero pure tensor section is linear in its first argument. -/
theorem degreeZeroSectionValue_smul_left (r : 𝒜 0) (m : ℳ 0) (n : ℵ 0) :
    degreeZeroSectionValue 𝒜 ℳ ℵ (r • m) n =
      r • degreeZeroSectionValue 𝒜 ℳ ℵ m n := sorry

/-- The right-input pure-tensor section map is additive in its fixed first input. -/
theorem degreeZeroSectionRight_add (m₁ m₂ : ℳ 0) :
    degreeZeroSectionRight 𝒜 ℳ ℵ (m₁ + m₂) =
      degreeZeroSectionRight 𝒜 ℳ ℵ m₁ +
        degreeZeroSectionRight 𝒜 ℳ ℵ m₂ := sorry

/-- The right-input pure-tensor section map is linear in its fixed first input. -/
theorem degreeZeroSectionRight_smul (r : 𝒜 0) (m : ℳ 0) :
    degreeZeroSectionRight 𝒜 ℳ ℵ (r • m) =
      r • degreeZeroSectionRight 𝒜 ℳ ℵ m := sorry

/-- The bilinear pure-tensor section map on degree-zero homogeneous elements. -/
noncomputable def degreeZeroSectionPairing :
    ℳ 0 →ₗ[𝒜 0] ℵ 0 →ₗ[𝒜 0]
      (ModuleCat.restrictScalars (AssociatedModule.degreeZeroRingHom 𝒜)).obj
        ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
          (AssociatedModule.sheaf 𝒜 ℵ)).val.obj (op ⊤)) where
  toFun := degreeZeroSectionRight 𝒜 ℳ ℵ
  map_add' := degreeZeroSectionRight_add 𝒜 ℳ ℵ
  map_smul' := degreeZeroSectionRight_smul 𝒜 ℳ ℵ

/-- The tensor product of the two degree-zero section maps. -/
noncomputable def degreeZeroSectionMap :
    ℳ 0 ⊗[𝒜 0] ℵ 0 →ₗ[𝒜 0]
      (ModuleCat.restrictScalars (AssociatedModule.degreeZeroRingHom 𝒜)).obj
        ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
          (AssociatedModule.sheaf 𝒜 ℵ)).val.obj (op ⊤)) :=
  TensorProduct.lift (degreeZeroSectionPairing 𝒜 ℳ ℵ)

/-- The tensor product of the two degree-zero section maps, bundled in `ModuleCat`. -/
noncomputable def degreeZeroSectionHom :
    ModuleCat.of (𝒜 0) (ℳ 0 ⊗[𝒜 0] ℵ 0) ⟶
      (ModuleCat.restrictScalars (AssociatedModule.degreeZeroRingHom 𝒜)).obj
        ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
          (AssociatedModule.sheaf 𝒜 ℵ)).val.obj (op ⊤)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (𝒜 0) (ℳ 0 ⊗[𝒜 0] ℵ 0))
    (Y := (ModuleCat.restrictScalars (AssociatedModule.degreeZeroRingHom 𝒜)).obj
      ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
        (AssociatedModule.sheaf 𝒜 ℵ)).val.obj (op ⊤)))
    (degreeZeroSectionMap 𝒜 ℳ ℵ)

/-- The degree-zero tensor-section morphism sends a pure tensor to the pure tensor of the
corresponding global associated sections. -/
@[simp]
theorem degreeZeroSectionHom_tmul (m : ℳ 0) (n : ℵ 0) :
    degreeZeroSectionHom 𝒜 ℳ ℵ (m ⊗ₜ[𝒜 0] n) =
      tensorSectionLinear (AlgebraicGeometry.Proj 𝒜).sheaf
        (AssociatedModule.sheaf 𝒜 ℳ) (AssociatedModule.sheaf 𝒜 ℵ) (op ⊤)
          (AssociatedModule.degreeZeroSection 𝒜 ℳ m)
          (AssociatedModule.degreeZeroSection 𝒜 ℵ n) := sorry

/-! ## Positive standard opens -/

/-- The standard-open localized tensor comparison bundled as a module morphism. -/
@[stacks 01MK "standard-open tensor comparison morphism"]
noncomputable def awayHom {d : ℕ} (f : 𝒜 d) :
    ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A))
        (AssociatedModule.away 𝒜 ℳ f ⊗[HomogeneousLocalization.Away 𝒜 (f : A)]
          AssociatedModule.away 𝒜 ℵ f) ⟶
      ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A))
        (AssociatedModule.away 𝒜 (grading A ℳ ℵ) f) :=
  ModuleCat.ofHom (awayMap 𝒜 ℳ ℵ f)

/-- The pure tensor section determined by two homogeneous fractions on a standard open. -/
noncomputable def awaySectionValue {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m : AssociatedModule.away 𝒜 ℳ f) (n : AssociatedModule.away 𝒜 ℵ f) :
    (ModuleCat.restrictScalars
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
        ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
          (AssociatedModule.sheaf 𝒜 ℵ)).val.obj
            (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))) :=
  tensorSectionLinear (AlgebraicGeometry.Proj 𝒜).sheaf
    (AssociatedModule.sheaf 𝒜 ℳ) (AssociatedModule.sheaf 𝒜 ℵ)
      (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))
        (AssociatedModule.awaySection 𝒜 ℳ f hd m)
        (AssociatedModule.awaySection 𝒜 ℵ f hd n)

/-- The standard-open pure tensor section is additive in its second argument. -/
theorem awaySectionValue_add_right {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m : AssociatedModule.away 𝒜 ℳ f)
    (n₁ n₂ : AssociatedModule.away 𝒜 ℵ f) :
    awaySectionValue 𝒜 ℳ ℵ f hd m (n₁ + n₂) =
      awaySectionValue 𝒜 ℳ ℵ f hd m n₁ +
        awaySectionValue 𝒜 ℳ ℵ f hd m n₂ := sorry

/-- The standard-open pure tensor section is linear in its second argument. -/
theorem awaySectionValue_smul_right {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m : AssociatedModule.away 𝒜 ℳ f)
    (r : HomogeneousLocalization.Away 𝒜 (f : A))
    (n : AssociatedModule.away 𝒜 ℵ f) :
    awaySectionValue 𝒜 ℳ ℵ f hd m (r • n) =
      r • awaySectionValue 𝒜 ℳ ℵ f hd m n := sorry

/-- Fixing the first standard-open fraction gives a linear pure-tensor section map. -/
noncomputable def awaySectionRight {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m : AssociatedModule.away 𝒜 ℳ f) :
    AssociatedModule.away 𝒜 ℵ f →ₗ[HomogeneousLocalization.Away 𝒜 (f : A)]
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
          ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
            (AssociatedModule.sheaf 𝒜 ℵ)).val.obj
              (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))) where
  toFun := awaySectionValue 𝒜 ℳ ℵ f hd m
  map_add' := awaySectionValue_add_right 𝒜 ℳ ℵ f hd m
  map_smul' := awaySectionValue_smul_right 𝒜 ℳ ℵ f hd m

/-- The standard-open pure tensor section is additive in its first argument. -/
theorem awaySectionValue_add_left {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m₁ m₂ : AssociatedModule.away 𝒜 ℳ f)
    (n : AssociatedModule.away 𝒜 ℵ f) :
    awaySectionValue 𝒜 ℳ ℵ f hd (m₁ + m₂) n =
      awaySectionValue 𝒜 ℳ ℵ f hd m₁ n +
        awaySectionValue 𝒜 ℳ ℵ f hd m₂ n := sorry

/-- The standard-open pure tensor section is linear in its first argument. -/
theorem awaySectionValue_smul_left {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (r : HomogeneousLocalization.Away 𝒜 (f : A))
    (m : AssociatedModule.away 𝒜 ℳ f) (n : AssociatedModule.away 𝒜 ℵ f) :
    awaySectionValue 𝒜 ℳ ℵ f hd (r • m) n =
      r • awaySectionValue 𝒜 ℳ ℵ f hd m n := sorry

/-- The right-input standard-open tensor-section map is additive in its first input. -/
theorem awaySectionRight_add {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m₁ m₂ : AssociatedModule.away 𝒜 ℳ f) :
    awaySectionRight 𝒜 ℳ ℵ f hd (m₁ + m₂) =
      awaySectionRight 𝒜 ℳ ℵ f hd m₁ +
        awaySectionRight 𝒜 ℳ ℵ f hd m₂ := sorry

/-- The right-input standard-open tensor-section map is linear in its first input. -/
theorem awaySectionRight_smul {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (r : HomogeneousLocalization.Away 𝒜 (f : A))
    (m : AssociatedModule.away 𝒜 ℳ f) :
    awaySectionRight 𝒜 ℳ ℵ f hd (r • m) =
      r • awaySectionRight 𝒜 ℳ ℵ f hd m := sorry

/-- The bilinear pure-tensor section map on a positive standard open. -/
noncomputable def awaySectionPairing {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    AssociatedModule.away 𝒜 ℳ f →ₗ[HomogeneousLocalization.Away 𝒜 (f : A)]
      AssociatedModule.away 𝒜 ℵ f →ₗ[HomogeneousLocalization.Away 𝒜 (f : A)]
        (ModuleCat.restrictScalars
          (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
            ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
              (AssociatedModule.sheaf 𝒜 ℵ)).val.obj
                (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))) where
  toFun := awaySectionRight 𝒜 ℳ ℵ f hd
  map_add' := awaySectionRight_add 𝒜 ℳ ℵ f hd
  map_smul' := awaySectionRight_smul 𝒜 ℳ ℵ f hd

/-- The tensor product of the two standard-open fraction-to-section maps. -/
noncomputable def awaySectionMap {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    AssociatedModule.away 𝒜 ℳ f ⊗[HomogeneousLocalization.Away 𝒜 (f : A)]
        AssociatedModule.away 𝒜 ℵ f →ₗ[HomogeneousLocalization.Away 𝒜 (f : A)]
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
          ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
            (AssociatedModule.sheaf 𝒜 ℵ)).val.obj
              (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))) :=
  TensorProduct.lift (awaySectionPairing 𝒜 ℳ ℵ f hd)

/-- The tensor product of the two standard-open section maps, bundled in `ModuleCat`. -/
noncomputable def awaySectionHom {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A))
        (AssociatedModule.away 𝒜 ℳ f ⊗[HomogeneousLocalization.Away 𝒜 (f : A)]
          AssociatedModule.away 𝒜 ℵ f) ⟶
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
          ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
            (AssociatedModule.sheaf 𝒜 ℵ)).val.obj
              (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A))
      (AssociatedModule.away 𝒜 ℳ f ⊗[HomogeneousLocalization.Away 𝒜 (f : A)]
        AssociatedModule.away 𝒜 ℵ f))
    (Y := (ModuleCat.restrictScalars
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
        ((moduleTensor (AssociatedModule.sheaf 𝒜 ℳ)
          (AssociatedModule.sheaf 𝒜 ℵ)).val.obj
            (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))))
    (awaySectionMap 𝒜 ℳ ℵ f hd)

/-- The standard-open tensor-section morphism sends a pure tensor to the corresponding pure
tensor of associated fraction sections. -/
@[simp]
theorem awaySectionHom_tmul {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m : AssociatedModule.away 𝒜 ℳ f) (n : AssociatedModule.away 𝒜 ℵ f) :
    awaySectionHom 𝒜 ℳ ℵ f hd
        (m ⊗ₜ[HomogeneousLocalization.Away 𝒜 (f : A)] n) =
      tensorSectionLinear (AlgebraicGeometry.Proj 𝒜).sheaf
        (AssociatedModule.sheaf 𝒜 ℳ) (AssociatedModule.sheaf 𝒜 ℵ)
          (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))
            (AssociatedModule.awaySection 𝒜 ℳ f hd m)
            (AssociatedModule.awaySection 𝒜 ℵ f hd n) := sorry

/-! ## Stalks -/

/-- The point-localized tensor value, regarded over the structure-sheaf stalk. -/
noncomputable def stalkValue (x : AlgebraicGeometry.Proj 𝒜)
    (m : AssociatedModule.atPoint 𝒜 ℳ x) (n : AssociatedModule.atPoint 𝒜 ℵ x) :
    AssociatedModule.atPoint 𝒜 (grading A ℳ ℵ) x :=
  atPointMap 𝒜 ℳ ℵ x
    (m ⊗ₜ[HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl] n)

/-- The stalk tensor value is additive in its second argument. -/
theorem stalkValue_add_right (x : AlgebraicGeometry.Proj 𝒜)
    (m : AssociatedModule.atPoint 𝒜 ℳ x)
    (n₁ n₂ : AssociatedModule.atPoint 𝒜 ℵ x) :
    stalkValue 𝒜 ℳ ℵ x m (n₁ + n₂) =
      stalkValue 𝒜 ℳ ℵ x m n₁ +
        stalkValue 𝒜 ℳ ℵ x m n₂ := sorry

/-- The stalk tensor value is linear in its second argument. -/
theorem stalkValue_smul_right (x : AlgebraicGeometry.Proj 𝒜)
    (m : AssociatedModule.atPoint 𝒜 ℳ x)
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
    (n : AssociatedModule.atPoint 𝒜 ℵ x) :
    stalkValue 𝒜 ℳ ℵ x m (r • n) =
      r • stalkValue 𝒜 ℳ ℵ x m n := sorry

/-- Fixing the first point-localized factor gives a stalk-linear map in the second factor. -/
noncomputable def stalkRight (x : AlgebraicGeometry.Proj 𝒜)
    (m : AssociatedModule.atPoint 𝒜 ℳ x) :
    AssociatedModule.atPoint 𝒜 ℵ x →ₗ[(AlgebraicGeometry.Proj 𝒜).presheaf.stalk x]
      AssociatedModule.atPoint 𝒜 (grading A ℳ ℵ) x where
  toFun := stalkValue 𝒜 ℳ ℵ x m
  map_add' := stalkValue_add_right 𝒜 ℳ ℵ x m
  map_smul' := stalkValue_smul_right 𝒜 ℳ ℵ x m

/-- The stalk tensor value is additive in its first argument. -/
theorem stalkValue_add_left (x : AlgebraicGeometry.Proj 𝒜)
    (m₁ m₂ : AssociatedModule.atPoint 𝒜 ℳ x)
    (n : AssociatedModule.atPoint 𝒜 ℵ x) :
    stalkValue 𝒜 ℳ ℵ x (m₁ + m₂) n =
      stalkValue 𝒜 ℳ ℵ x m₁ n +
        stalkValue 𝒜 ℳ ℵ x m₂ n := sorry

/-- The stalk tensor value is linear in its first argument. -/
theorem stalkValue_smul_left (x : AlgebraicGeometry.Proj 𝒜)
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
    (m : AssociatedModule.atPoint 𝒜 ℳ x) (n : AssociatedModule.atPoint 𝒜 ℵ x) :
    stalkValue 𝒜 ℳ ℵ x (r • m) n =
      r • stalkValue 𝒜 ℳ ℵ x m n := sorry

/-- The right-input stalk tensor map is additive in its fixed first input. -/
theorem stalkRight_add (x : AlgebraicGeometry.Proj 𝒜)
    (m₁ m₂ : AssociatedModule.atPoint 𝒜 ℳ x) :
    stalkRight 𝒜 ℳ ℵ x (m₁ + m₂) =
      stalkRight 𝒜 ℳ ℵ x m₁ +
        stalkRight 𝒜 ℳ ℵ x m₂ := sorry

/-- The right-input stalk tensor map is linear in its fixed first input. -/
theorem stalkRight_smul (x : AlgebraicGeometry.Proj 𝒜)
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
    (m : AssociatedModule.atPoint 𝒜 ℳ x) :
    stalkRight 𝒜 ℳ ℵ x (r • m) =
      r • stalkRight 𝒜 ℳ ℵ x m := sorry

/-- The stalk-bilinear pairing induced by the point-localized tensor comparison. -/
noncomputable def stalkPairing (x : AlgebraicGeometry.Proj 𝒜) :
    AssociatedModule.atPoint 𝒜 ℳ x →ₗ[(AlgebraicGeometry.Proj 𝒜).presheaf.stalk x]
      AssociatedModule.atPoint 𝒜 ℵ x →ₗ[(AlgebraicGeometry.Proj 𝒜).presheaf.stalk x]
        AssociatedModule.atPoint 𝒜 (grading A ℳ ℵ) x where
  toFun := stalkRight 𝒜 ℳ ℵ x
  map_add' := stalkRight_add 𝒜 ℳ ℵ x
  map_smul' := stalkRight_smul 𝒜 ℳ ℵ x

/-- The point-localized tensor comparison, regarded as a linear map over the structure-sheaf
stalk through the canonical stalk identification. -/
@[stacks 01MK "stalk tensor comparison"]
noncomputable def stalkMap (x : AlgebraicGeometry.Proj 𝒜) :
    AssociatedModule.atPoint 𝒜 ℳ x ⊗[(AlgebraicGeometry.Proj 𝒜).presheaf.stalk x]
        AssociatedModule.atPoint 𝒜 ℵ x →ₗ[(AlgebraicGeometry.Proj 𝒜).presheaf.stalk x]
      AssociatedModule.atPoint 𝒜 (grading A ℳ ℵ) x :=
  TensorProduct.lift (stalkPairing 𝒜 ℳ ℵ x)

/-- The stalk-linear point comparison agrees with `atPointMap` on pure tensors. -/
@[simp]
theorem stalkMap_tmul (x : AlgebraicGeometry.Proj 𝒜)
    (m : AssociatedModule.atPoint 𝒜 ℳ x) (n : AssociatedModule.atPoint 𝒜 ℵ x) :
    stalkMap 𝒜 ℳ ℵ x
        (m ⊗ₜ[(AlgebraicGeometry.Proj 𝒜).presheaf.stalk x] n) =
      atPointMap 𝒜 ℳ ℵ x
        (m ⊗ₜ[HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl] n) := sorry

/-- The point comparison as a morphism of modules over the structure-sheaf stalk. -/
noncomputable def stalkHom (x : AlgebraicGeometry.Proj 𝒜) :
    ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
        (AssociatedModule.atPoint 𝒜 ℳ x ⊗[(AlgebraicGeometry.Proj 𝒜).presheaf.stalk x]
          AssociatedModule.atPoint 𝒜 ℵ x) ⟶
      ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
        (AssociatedModule.atPoint 𝒜 (grading A ℳ ℵ) x) :=
  ModuleCat.ofHom (stalkMap 𝒜 ℳ ℵ x)

/-! ## Comparison squares -/

variable [decompM : DirectSum.Decomposition ℳ] [decompN : DirectSum.Decomposition ℵ]

include decompM decompN

/-- The global degree-zero square for the associated tensor morphism commutes over the
degree-zero ring. -/
@[stacks 01MK "global degree-zero square for the associated tensor morphism"]
theorem globalSections :
    CommSq (degreeZeroHom 𝒜 ℳ ℵ) (degreeZeroSectionHom 𝒜 ℳ ℵ)
      (AssociatedModule.degreeZeroToGlobalSectionsHom 𝒜 (grading A ℳ ℵ))
      ((ModuleCat.restrictScalars (AssociatedModule.degreeZeroRingHom 𝒜)).map
        ((hom 𝒜 ℳ ℵ).val.app (op ⊤))) := sorry

/-- On a pure degree-zero tensor, the global-section square compares the two canonical tensor
sections. -/
theorem globalSections_tmul (m : ℳ 0) (n : ℵ 0) :
    AssociatedModule.degreeZeroToGlobalSectionsHom 𝒜 (grading A ℳ ℵ)
        (degreeZeroHom 𝒜 ℳ ℵ (m ⊗ₜ[𝒜 0] n)) =
      (ModuleCat.restrictScalars (AssociatedModule.degreeZeroRingHom 𝒜)).map
          ((hom 𝒜 ℳ ℵ).val.app (op ⊤))
        (degreeZeroSectionHom 𝒜 ℳ ℵ (m ⊗ₜ[𝒜 0] n)) := sorry

/-- On a positive standard open, the associated tensor morphism and localized tensor
comparison form a commutative square. -/
@[stacks 01MK "standard-open square for the associated tensor morphism"]
theorem away {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    CommSq (awayHom 𝒜 ℳ ℵ f) (awaySectionHom 𝒜 ℳ ℵ f hd)
      (AssociatedModule.awaySectionHom 𝒜 (grading A ℳ ℵ) f hd)
      ((ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).map
          ((hom 𝒜 ℳ ℵ).val.app
            (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))))) := sorry

/-- On pure localized tensors, the standard-open square compares the two canonical tensor
sections. -/
theorem away_tmul {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m : AssociatedModule.away 𝒜 ℳ f) (n : AssociatedModule.away 𝒜 ℵ f) :
    AssociatedModule.awaySectionHom 𝒜 (grading A ℳ ℵ) f hd
        (awayHom 𝒜 ℳ ℵ f
          (m ⊗ₜ[HomogeneousLocalization.Away 𝒜 (f : A)] n)) =
      (ModuleCat.restrictScalars
          (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).map
            ((hom 𝒜 ℳ ℵ).val.app
              (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))))
        (awaySectionHom 𝒜 ℳ ℵ f hd
          (m ⊗ₜ[HomogeneousLocalization.Away 𝒜 (f : A)] n)) := sorry

/-- The stalk tensor comparison is the localized tensor comparison under the canonical stalk
evaluations. -/
@[stacks 01MK "stalk square for the associated tensor morphism"]
theorem stalk (x : AlgebraicGeometry.Proj 𝒜) :
    CommSq
      (RingedSpace.moduleStalkHom x (hom 𝒜 ℳ ℵ))
      ((RingedSpace.Tensor.Stalk.comparisonIso
          (AssociatedModule.sheaf 𝒜 ℳ) (AssociatedModule.sheaf 𝒜 ℵ) x).hom ≫
        (AssociatedModule.stalkToPointLinearMap 𝒜 ℳ x ⊗ₘ
          AssociatedModule.stalkToPointLinearMap 𝒜 ℵ x))
      (AssociatedModule.stalkToPointLinearMap 𝒜 (grading A ℳ ℵ) x)
      (stalkHom 𝒜 ℳ ℵ x) := sorry

end AlgebraicGeometry.Proj.AssociatedModule.Tensor
