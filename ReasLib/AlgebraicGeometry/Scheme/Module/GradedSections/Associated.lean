/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Functorial
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionRingProj

/-!
# Associated sheaves of twisted section modules

The full integer-graded module of twisted global sections has a canonical internal grading.
This module applies the associated-module construction over the exact internal grading of the
section ring and packages its functoriality and degree-zero comparison.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.GradedSections

variable {X : Scheme.{u}}
variable (L : X.Modules) [Invertible L]

/-- The internal degree-`n` submodule of the full twisted-section direct sum. -/
abbrev twistedInternalGrading (F : X.Modules) (n : ℤ) :
    Submodule ℤ (RingedSpace.GradedSections.twisted L F) :=
  LinearMap.range
    (DirectSum.lof ℤ ℤ (RingedSpace.GradedSections.twistedDegree L F) n)

/-- The explicit decomposition of twisted sections into their internal homogeneous submodules. -/
noncomputable def twistedInternalDecompose (F : X.Modules) :
    RingedSpace.GradedSections.twisted L F →+
      ⨁ n : ℤ, twistedInternalGrading L F n :=
  (DirectSum.congrAddEquiv
    (fun n ↦ (LinearEquiv.ofInjective
      (DirectSum.lof ℤ ℤ (RingedSpace.GradedSections.twistedDegree L F) n) (by
        intro x y h
        exact DirectSum.of_injective n (by
          simpa only [DirectSum.lof_eq_of] using h))).toAddEquiv)).toAddMonoidHom

/-- Recomposition after the explicit internal decomposition is the identity. -/
theorem twistedInternalDecompose_left_inv (F : X.Modules)
    (x : RingedSpace.GradedSections.twisted L F) :
    DirectSum.coeAddMonoidHom (twistedInternalGrading L F)
      (twistedInternalDecompose L F x) = x := sorry

/-- Decomposition after canonical recomposition is the identity. -/
theorem twistedInternalDecompose_right_inv (F : X.Modules)
    (x : ⨁ n : ℤ, twistedInternalGrading L F n) :
    twistedInternalDecompose L F
      (DirectSum.coeAddMonoidHom (twistedInternalGrading L F) x) = x := sorry

/-- The internal homogeneous submodules give the canonical decomposition of twisted sections. -/
noncomputable instance instDecompositionTwistedInternalGrading (F : X.Modules) :
    DirectSum.Decomposition (twistedInternalGrading L F) where
  decompose' := twistedInternalDecompose L F
  left_inv := twistedInternalDecompose_left_inv L F
  right_inv := twistedInternalDecompose_right_inv L F

/-- A homogeneous section-ring element sends an internal twisted component to the component of
the sum of the degrees. -/
theorem smul_mem_twistedInternalGrading (F : X.Modules) {m : ℕ} {n : ℤ}
    (a : RingedSpace.GradedSections.grading L m)
    (x : twistedInternalGrading L F n) :
    (a : RingedSpace.GradedSections.ring L) •
        (x : RingedSpace.GradedSections.twisted L F) ∈
      twistedInternalGrading L F ((m : ℤ) + n) := sorry

/-- The section-ring grading acts compatibly on the internal grading of twisted sections. -/
noncomputable instance instGradedSMulTwistedInternalGrading (F : X.Modules) :
    SetLike.GradedSMul (RingedSpace.GradedSections.grading L)
      (twistedInternalGrading L F) where
  smul_mem := fun {i j} a x ha hx ↦ by
    simpa [AddAction.nat_vadd_int] using
      smul_mem_twistedInternalGrading L F
        (a := ⟨a, ha⟩) (x := ⟨x, hx⟩)

/-- The additive map on full twisted-section sums induced degreewise by a module-sheaf
morphism. -/
noncomputable def twistedMapAddHom {F G : X.Modules} (φ : F ⟶ G) :
    RingedSpace.GradedSections.twisted L F →+
      RingedSpace.GradedSections.twisted L G :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (RingedSpace.GradedSections.twistedDegree L G) n).comp
      (((φ ⊗ₘ 𝟙 (L ^⊗ n)).val.app (op ⊤)).hom).toAddMonoidHom

/-- The degreewise map on twisted sections commutes with the section-ring action. -/
theorem twistedMapAddHom_smul {F G : X.Modules} (φ : F ⟶ G)
    (r : RingedSpace.GradedSections.ring L)
    (x : RingedSpace.GradedSections.twisted L F) :
    twistedMapAddHom L φ (r • x) = r • twistedMapAddHom L φ x := sorry

/-- A module-sheaf morphism induces a linear map on its full twisted-section module. -/
noncomputable def twistedMap {F G : X.Modules} (φ : F ⟶ G) :
    RingedSpace.GradedSections.twisted L F →ₗ[RingedSpace.GradedSections.ring L]
      RingedSpace.GradedSections.twisted L G :=
  { twistedMapAddHom L φ with
    map_smul' := twistedMapAddHom_smul L φ }

/-- The induced map on twisted sections preserves every internal homogeneous component. -/
theorem twistedMap_mem_internalGrading {F G : X.Modules} (φ : F ⟶ G) (n : ℤ) :
    Set.MapsTo (twistedMap L φ) (twistedInternalGrading L F n)
      (twistedInternalGrading L G n) := sorry

/-- The sheaf on the section-ring projective spectrum associated to the full twisted-section
module. -/
noncomputable def associatedTwistedSheaf (F : X.Modules) :
    (Proj (RingedSpace.GradedSections.grading L)).Modules :=
  Proj.AssociatedModule.sheaf (RingedSpace.GradedSections.grading L)
    (twistedInternalGrading L F)

/-- A module-sheaf morphism induces the canonical morphism between the associated twisted-section
sheaves. -/
noncomputable def associatedTwistedMap {F G : X.Modules} (φ : F ⟶ G) :
    associatedTwistedSheaf L F ⟶ associatedTwistedSheaf L G :=
  Proj.AssociatedModule.map (RingedSpace.GradedSections.grading L)
    (twistedInternalGrading L F) (twistedInternalGrading L G)
    (twistedMap L φ) (twistedMap_mem_internalGrading L φ)

/-- The associated twisted-section map induced by an identity is an identity. -/
theorem associatedTwistedMap_id (F : X.Modules) :
    associatedTwistedMap L (𝟙 F) = 𝟙 (associatedTwistedSheaf L F) := sorry

/-- Associated twisted-section maps preserve composition. -/
theorem associatedTwistedMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) :
    associatedTwistedMap L (φ ≫ ψ) =
      associatedTwistedMap L φ ≫ associatedTwistedMap L ψ := sorry

/-- Taking the associated sheaf of the full twisted-section module is functorial in the module
sheaf. -/
noncomputable def associatedTwistedFunctor :
    X.Modules ⥤ (Proj (RingedSpace.GradedSections.grading L)).Modules where
  obj F := associatedTwistedSheaf L F
  map φ := associatedTwistedMap L φ
  map_id F := associatedTwistedMap_id L F
  map_comp φ ψ := associatedTwistedMap_comp L φ ψ

/-- The internal degree-zero component of twisted sections is canonically the global sections of
the original module sheaf. -/
noncomputable def twistedDegreeZeroIso (F : X.Modules) :
    twistedInternalGrading L F 0 ≃ₗ[ℤ] F.val.obj (op ⊤) :=
  let e : F ⊗ (L ^⊗ (0 : ℤ)) ≅ F :=
    (Iso.refl F ⊗ᵢ RingedSpace.InvertiblePower.zeroIso L) ≪≫
      (Iso.refl F ⊗ᵢ RingedSpace.unitIsoTensorUnit X.toRingedSpace) ≪≫ ρ_ F
  let eTop :=
    (SheafOfModules.evaluation X.toRingedSpace.ringCatSheaf (op ⊤)).mapIso e
  (LinearEquiv.ofInjective
      (DirectSum.lof ℤ ℤ (RingedSpace.GradedSections.twistedDegree L F) 0) (by
        intro x y h
        exact DirectSum.of_injective 0 (by
          simpa only [DirectSum.lof_eq_of] using h))).symm.trans
    (LinearEquiv.restrictScalars ℤ eTop.toLinearEquiv)

/-- The canonical degree-zero map from twisted sections to global sections of their associated
sheaf. -/
noncomputable def degreeZeroToAssociatedTwistedGlobalSections (F : X.Modules) :=
  Proj.AssociatedModule.degreeZeroToGlobalSections
    (RingedSpace.GradedSections.grading L) (twistedInternalGrading L F)

end AlgebraicGeometry.Scheme.Modules.GradedSections
