module

public import Mathlib.CategoryTheory.Limits.Lattice
public import stacks_project.Chap20.Open_cover_module_cech_explicit

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

local notation "ModX" => RingedSpace.Modules X

section

variable [HasProducts ModX]

noncomputable abbrev openCoverModuleCechTermFamily
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) :
    ℕ → ModX :=
  fun p ↦ openCoverModuleCechTerm 𝒰 ℱ p

noncomputable abbrev openCoverModuleCechDifferentialFamily
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) :
    (p : ℕ) → openCoverModuleCechTermFamily 𝒰 ℱ p ⟶
      openCoverModuleCechTermFamily 𝒰 ℱ (p + 1) :=
  fun p ↦ openCoverModuleCechDifferential 𝒰 ℱ p

/-- The module-valued Čech complex of `ℱ` for the indexed open cover `𝒰`. -/
noncomputable def openCoverModuleCechComplex
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) :
    CochainComplex ModX ℕ :=
  CochainComplex.of
    (openCoverModuleCechTermFamily 𝒰 ℱ)
    (openCoverModuleCechDifferentialFamily 𝒰 ℱ)
    (openCoverModuleCechDifferential_comp 𝒰 ℱ)

end

section

variable [hP : HasProducts ModX]

omit hP in
@[simp] theorem openCoverModuleCechComplex_X
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ) :
    (openCoverModuleCechComplex 𝒰 ℱ).X p = openCoverModuleCechTerm 𝒰 ℱ p :=
  rfl

omit hP in
@[simp] theorem openCoverModuleCechComplex_d
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ) :
    (openCoverModuleCechComplex 𝒰 ℱ).d p (p + 1) =
      openCoverModuleCechDifferential 𝒰 ℱ p := by
  simpa [openCoverModuleCechComplex] using
    (CochainComplex.of_d
      (openCoverModuleCechTermFamily 𝒰 ℱ)
      (openCoverModuleCechDifferentialFamily 𝒰 ℱ)
      (openCoverModuleCechDifferential_comp 𝒰 ℱ)
      p)

end

section

variable [HasProducts ModX]
variable [HasZeroObject ModX]

/-- The canonical augmentation from `ℱ` to its module-valued Čech complex for `𝒰`. -/
noncomputable def openCoverModuleCechAugmentation
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) :
    (CochainComplex.single₀ ModX).obj ℱ ⟶ openCoverModuleCechComplex 𝒰 ℱ :=
  (CochainComplex.fromSingle₀Equiv (openCoverModuleCechComplex 𝒰 ℱ) ℱ).symm
    ⟨openCoverModuleCechAugmentationMap 𝒰 ℱ,
      openCoverModuleCechAugmentationMap_comp_d_zero_one 𝒰 ℱ⟩

end

section

variable [HasProducts ModX]

@[simp] theorem openCoverModuleCechAugmentation_f_zero
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) :
    (openCoverModuleCechAugmentation 𝒰 ℱ).f 0 =
      openCoverModuleCechAugmentationMap 𝒰 ℱ := sorry

end

end AlgebraicGeometry.RingedSpace
