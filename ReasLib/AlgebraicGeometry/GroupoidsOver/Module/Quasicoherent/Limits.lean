/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.Exactness
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Exactness
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.FiniteLimits

/-! # Images and kernel comparisons for quasi-coherent modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The ambient cokernel of a morphism of quasi-coherent modules is quasi-coherent. -/
instance isQuasicoherent_cokernel {F G : QCoh X} (φ : F ⟶ G) :
    (cokernel ((inclusion X).map φ)).IsQuasicoherent :=
  sorry

/-- The canonical comparison from the included quasi-coherent image to the ambient image. -/
def inclusion_imageComparison {F G : QCoh X} (φ : F ⟶ G) :
    (inclusion X).obj (Abelian.image φ) ⟶ Abelian.image ((inclusion X).map φ) :=
  kernelComparison (cokernel.π φ) (inclusion X) ≫
    (kernel.mapIso ((inclusion X).map (cokernel.π φ))
      (cokernel.π ((inclusion X).map φ)) (Iso.refl _)
      (PreservesCokernel.iso (inclusion X) φ)
      (PreservesCokernel.π_iso_hom (inclusion X) φ)).hom

/-- The image comparison commutes with the canonical inclusions into the target module. -/
theorem inclusion_imageComparison_comp_ι {F G : QCoh X} (φ : F ⟶ G) :
    inclusion_imageComparison φ ≫ Abelian.image.ι ((inclusion X).map φ) =
      (inclusion X).map (Abelian.image.ι φ) :=
  sorry

/-- The quasi-coherent and ambient images agree under the canonical comparison. -/
instance inclusion_imageComparison_isIso {F G : QCoh X} (φ : F ⟶ G) :
    IsIso (inclusion_imageComparison φ) :=
  sorry

/-- The ambient image of a morphism of quasi-coherent modules is quasi-coherent. -/
instance isQuasicoherent_image {F G : QCoh X} (φ : F ⟶ G) :
    (Abelian.image ((inclusion X).map φ)).IsQuasicoherent :=
  sorry

/-- The ambient fppf kernel restricts to a locally quasi-coherent étale module
with flat base change. -/
theorem kernel_mem_lqcohFbc {F G : QCoh X} (φ : F ⟶ G) :
    FppfModules.lqcohFbc X (kernel ((inclusion X).map φ)) :=
  sorry

/-- The intrinsic kernel is the quasi-coherent coreflection of the kernel
in locally quasi-coherent étale modules with flat base change. -/
def kernelIso_toQCoh {F G : QCoh X} (φ : F ⟶ G) :
    kernel φ ≅ (LQCohFbc.toQCoh X).obj (kernel ((toLQCohFbc X).map φ)) :=
  (PreservesKernel.iso (LQCohFbc.toQCoh X) ((toLQCohFbc X).map φ) ≪≫
    kernel.mapIso ((toLQCohFbc X ⋙ LQCohFbc.toQCoh X).map φ) φ
      ((toLQCohFbc_comp_toQCoh X).app F) ((toLQCohFbc_comp_toQCoh X).app G)
      ((toLQCohFbc_comp_toQCoh X).hom.naturality φ)).symm

/-- The étale restriction of the ambient fppf kernel, bundled with local
quasi-coherence and flat base change. -/
def kernelLQCohFbc {F G : QCoh X} (φ : F ⟶ G) : LQCohFbc X :=
  ⟨(restriction X).obj (kernel ((inclusion X).map φ)), kernel_mem_lqcohFbc φ⟩

/-- The kernel after restriction to locally quasi-coherent modules with flat
base change agrees canonically with the restriction of the ambient fppf kernel. -/
def kernelRestrictionIso {F G : QCoh X} (φ : F ⟶ G) :
    kernel ((toLQCohFbc X).map φ) ≅ kernelLQCohFbc φ :=
  (lqcohFbc X).isoMk
    (PreservesKernel.iso (LQCohFbc.inclusion X) ((toLQCohFbc X).map φ) ≪≫
      (PreservesKernel.iso
        (SheafOfModules.pushforward.{u} (etaleToFppfStructureSheafMap X))
        ((inclusion X).map φ)).symm)

/-- The intrinsic quasi-coherent kernel is the coreflection of the étale
restriction of the actual ambient fppf kernel. -/
def kernelIso_toQCoh_fppf {F G : QCoh X} (φ : F ⟶ G) :
    kernel φ ≅ (LQCohFbc.toQCoh X).obj (kernelLQCohFbc φ) :=
  kernelIso_toQCoh φ ≪≫ (LQCohFbc.toQCoh X).mapIso (kernelRestrictionIso φ)

end AlgebraicGeometry.GroupoidsOver.QCoh
