/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.RingTheory.Kaehler.ExtendedConormal

/-!
# Kähler comparison maps for residue-identified Artinian local algebras

Morphisms induce canonical maps on residue-field tensors of Kähler differentials
and on the images of the extended conormal differentials.
-/

@[expose] public section

open CategoryTheory KaehlerDifferential
open scoped TensorProduct

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

/-- The algebra structure on the target carrier induced by a morphism of local algebras. -/
@[reducible] def algebraOfHom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    Algebra B.carrier A.carrier :=
  f.hom.toRingHom.toAlgebra

/-- The algebra structure induced by a morphism is compatible with the base algebra structures. -/
theorem algebraOfHom_isScalarTower {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    @IsScalarTower Λ B.carrier A.carrier _ (algebraOfHom f).toSMul _ := sorry

/-- A residue-compatible morphism induces a compatible tower to the identified residue field. -/
theorem algebraOfHom_residue_isScalarTower {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    @IsScalarTower B.carrier A.carrier k (algebraOfHom f).toSMul _ _ := sorry

/-- The image of the extended conormal differential in the residue-field tensor of Kähler
differentials. -/
abbrev conormalRange (A : ArtinianLocalAlgCat Λ k) :
    Submodule k (k ⊗[A.carrier] Ω[A.carrier⁄Λ]) :=
  LinearMap.range (kerCotangentToTensor_extend Λ A.carrier k (toResidueHom_surjective A))

/-- Membership in the conormal image is equivalent to being a value of the extended conormal
differential. -/
theorem mem_conormalRange {A : ArtinianLocalAlgCat Λ k}
    {tensor : k ⊗[A.carrier] Ω[A.carrier⁄Λ]} :
    tensor ∈ conormalRange A ↔
      ∃ cotangent, kerCotangentToTensor_extend Λ A.carrier k
        (toResidueHom_surjective A) cotangent = tensor :=
  sorry

namespace Hom

/-- The residue-field-linear map on tensors of Kähler differentials induced by a morphism. -/
def kaehlerTensorMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    k ⊗[B.carrier] Ω[B.carrier⁄Λ] →ₗ[k] k ⊗[A.carrier] Ω[A.carrier⁄Λ] :=
  @tensorMapBaseChange Λ B.carrier A.carrier k _ _ _ _ _ (algebraOfHom f) _
    (algebraOfHom_isScalarTower f) _ _ (algebraOfHom_residue_isScalarTower f)

/-- The induced Kähler tensor map sends a differential generator to the differential of its
image. -/
theorem kaehlerTensorMap_D {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (scalar : k) (element : B.carrier) :
    kaehlerTensorMap f (scalar ⊗ₜ[B.carrier] D Λ B.carrier element) =
      scalar ⊗ₜ[A.carrier] D Λ A.carrier (f.hom element) :=
  sorry

/-- The induced Kähler tensor map is linear in the residue-field scalar of a pure tensor. -/
theorem kaehlerTensorMap_tmul {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (scalar : k) (differential : Ω[B.carrier⁄Λ]) :
    kaehlerTensorMap f (scalar ⊗ₜ[B.carrier] differential) =
      scalar • kaehlerTensorMap f (1 ⊗ₜ[B.carrier] differential) :=
  sorry

/-- The induced Kähler tensor map preserves the images of the extended conormal differentials. -/
theorem kaehlerTensorMap_mapsTo_conormalRange {B A : ArtinianLocalAlgCat Λ k}
    (f : B ⟶ A) :
    ∀ tensor ∈ conormalRange B, kaehlerTensorMap f tensor ∈ conormalRange A :=
  sorry

/-- The restriction of the induced Kähler tensor map to the conormal images. -/
def conormalRangeMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    conormalRange B →ₗ[k] conormalRange A :=
  (kaehlerTensorMap f).restrict (kaehlerTensorMap_mapsTo_conormalRange f)

/-- The induced map on conormal images agrees with the Kähler tensor map on underlying tensors. -/
theorem conormalRangeMap_apply {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (tensor : conormalRange B) :
    (conormalRangeMap f tensor : k ⊗[A.carrier] Ω[A.carrier⁄Λ]) =
      kaehlerTensorMap f (tensor : k ⊗[B.carrier] Ω[B.carrier⁄Λ]) :=
  sorry

end Hom

end

end ArtinianLocalAlgCat
