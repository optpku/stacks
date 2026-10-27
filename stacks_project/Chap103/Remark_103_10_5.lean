/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Limits
import StacksCheckRecall

/-!
# Remark 103.10.5

On an algebraic stack, `QCoh` is abelian and its inclusion into `Mod` is right
exact but not exact. Cokernels and images of a map `φ` of quasi-coherent
modules agree in `Mod` and in `QCoh`, while the kernel computed in `Mod` lies
in `LQCoh^{fbc}` and `Q` of that kernel is the kernel in `QCoh`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/- Remark 103.10.5: quasi-coherent modules on an algebraic stack form an abelian category. -/
@[stacks 0GQL] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.instAbelian X : Abelian (QCoh X))

/- The inclusion is right exact. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_preservesFiniteColimits (X := X) :
  PreservesFiniteColimits (QCoh.inclusion X))

/- Exactness can fail, as witnessed by the affine scheme over the integers. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_not_exact :
  ¬ exactFunctor
    (QCoh (GroupoidsOver.slice (Over.mk (𝟙 (Spec (CommRingCat.of ℤ))))))
    (RingedSite.ModuleCat (ringedSite _)) (QCoh.inclusion _))

variable {F G : QCoh X} (φ : F ⟶ G)

/- The ambient cokernel agrees with the included intrinsic cokernel and is quasi-coherent. -/
#check (CategoryTheory.Limits.PreservesCokernel.iso (QCoh.inclusion X) φ :
  (QCoh.inclusion X).obj (cokernel φ) ≅ cokernel ((QCoh.inclusion X).map φ))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.isQuasicoherent_cokernel φ :
  (cokernel ((QCoh.inclusion X).map φ)).IsQuasicoherent)

/- The canonical image comparison is invertible and respects the image inclusions. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_imageComparison φ :
  (QCoh.inclusion X).obj (Abelian.image φ) ⟶ Abelian.image ((QCoh.inclusion X).map φ))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_imageComparison_comp_ι φ :
  QCoh.inclusion_imageComparison φ ≫ Abelian.image.ι ((QCoh.inclusion X).map φ) =
    (QCoh.inclusion X).map (Abelian.image.ι φ))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_imageComparison_isIso φ :
  IsIso (QCoh.inclusion_imageComparison φ))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.isQuasicoherent_image φ :
  (Abelian.image ((QCoh.inclusion X).map φ)).IsQuasicoherent)

/- The ambient kernel lies in locally quasi-coherent modules with flat base change. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh.kernel_mem_lqcohFbc φ :
  FppfModules.lqcohFbc X (kernel ((QCoh.inclusion X).map φ)))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.kernelLQCohFbc φ : LQCohFbc X)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.kernelRestrictionIso φ :
  kernel ((QCoh.toLQCohFbc X).map φ) ≅ QCoh.kernelLQCohFbc φ)

/- Applying the quasi-coherent coreflector to that restricted ambient kernel
recovers the intrinsic kernel. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh.kernelIso_toQCoh_fppf φ :
  kernel φ ≅ (LQCohFbc.toQCoh X).obj (QCoh.kernelLQCohFbc φ))
