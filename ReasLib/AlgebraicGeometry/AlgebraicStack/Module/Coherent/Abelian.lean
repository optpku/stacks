/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Limits

/-!
# Abelian category of coherent modules on a locally Noetherian algebraic stack

Ambient cokernels and images of coherent modules are coherent. Intrinsic kernels
are obtained by quasi-coherent coreflection of the restricted ambient kernel,
and the inclusion into quasi-coherent modules is exact.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- The zero sheaf of modules is coherent on a locally Noetherian algebraic stack. -/
instance coherentModuleProperty.containsZero :
    (coherentModuleProperty X).ContainsZero :=
  sorry

/-- Coherent modules on a locally Noetherian algebraic stack are closed under
cokernels in the category of all module sheaves. -/
instance coherentModuleProperty.isClosedUnderCokernels :
    (coherentModuleProperty X).IsClosedUnderCokernels :=
  sorry

/-- The ambient cokernel of a morphism between coherent modules is coherent. -/
instance isCoherent_cokernel {F G : SheafOfModules.{u} (structureSheaf X)}
    [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G] (φ : F ⟶ G) :
    AlgebraicStack.IsCoherent (cokernel φ) :=
  (coherentModuleProperty X).prop_cokernel φ inferInstance inferInstance

/-- The ambient image of a morphism between coherent modules is coherent. -/
instance isCoherent_image {F G : SheafOfModules.{u} (structureSheaf X)}
    [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G] (φ : F ⟶ G) :
    AlgebraicStack.IsCoherent (Abelian.image φ) :=
  sorry

/-- The intrinsic quasi-coherent kernel of a morphism between coherent modules
has coherent underlying module sheaf. -/
instance isCoherent_toQCoh_kernel {F G : Coh X} (φ : F ⟶ G) :
    AlgebraicStack.IsCoherent
      ((QCoh.inclusion X).obj (kernel (Coh.toQCoh.map φ))) :=
  sorry

namespace Coh

/-- Coherent modules on a locally Noetherian algebraic stack have finite products. -/
instance hasFiniteProducts : HasFiniteProducts (Coh X) :=
  sorry

/-- Coherent modules on a locally Noetherian algebraic stack have intrinsic kernels. -/
instance hasKernels : HasKernels (Coh X) :=
  sorry

/-- Every monomorphism of coherent modules on a locally Noetherian algebraic
stack is normal. -/
instance isNormalMonoCategory : IsNormalMonoCategory (Coh X) :=
  sorry

/-- Every epimorphism of coherent modules on a locally Noetherian algebraic
stack is normal. -/
instance isNormalEpiCategory : IsNormalEpiCategory (Coh X) :=
  sorry

/-- Coherent modules on a locally Noetherian algebraic stack form an abelian category. -/
instance abelian : Abelian (Coh X) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := isNormalMonoCategory
  toIsNormalEpiCategory := isNormalEpiCategory
  has_finite_products := hasFiniteProducts
  has_kernels := hasKernels
  has_cokernels := inferInstance

/-- The inclusion of coherent modules into all module sheaves preserves finite colimits. -/
instance inclusion_preservesFiniteColimits :
    PreservesFiniteColimits (inclusion X) :=
  sorry

/-- The inclusion of coherent modules into quasi-coherent modules preserves zero morphisms. -/
instance toQCoh_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (toQCoh : Coh X ⥤ QCoh X) where
  map_zero _ _ := rfl

/-- The inclusion of coherent modules into quasi-coherent modules preserves finite limits. -/
instance toQCoh_preservesFiniteLimits :
    PreservesFiniteLimits (toQCoh : Coh X ⥤ QCoh X) :=
  sorry

/-- The inclusion of coherent modules into quasi-coherent modules preserves finite colimits. -/
instance toQCoh_preservesFiniteColimits :
    PreservesFiniteColimits (toQCoh : Coh X ⥤ QCoh X) :=
  sorry

/-- The included coherent kernel is canonically the quasi-coherent coreflection
of the kernel in locally quasi-coherent étale modules with flat base change. -/
def kernelIso_toQCoh {F G : Coh X} (φ : F ⟶ G) :
    toQCoh.obj (kernel φ) ≅
      (LQCohFbc.toQCoh X).obj
        (kernel ((QCoh.toLQCohFbc X).map (toQCoh.map φ))) :=
  PreservesKernel.iso toQCoh φ ≪≫ QCoh.kernelIso_toQCoh (toQCoh.map φ)

/-- The included coherent kernel is canonically the quasi-coherent coreflection
of the étale restriction of the ambient fppf kernel. -/
def kernelIso_toQCoh_fppf {F G : Coh X} (φ : F ⟶ G) :
    toQCoh.obj (kernel φ) ≅
      (LQCohFbc.toQCoh X).obj (QCoh.kernelLQCohFbc (toQCoh.map φ)) :=
  PreservesKernel.iso toQCoh φ ≪≫ QCoh.kernelIso_toQCoh_fppf (toQCoh.map φ)

/-- The inclusion of coherent modules into quasi-coherent modules is exact. -/
theorem toQCoh_exact : exactFunctor (Coh X) (QCoh X) toQCoh :=
  ⟨toQCoh_preservesFiniteLimits, toQCoh_preservesFiniteColimits⟩

end Coh

/-- The quasi-coherent coreflection of the étale restriction of the ambient
fppf kernel of a morphism between coherent modules has coherent underlying sheaf. -/
instance isCoherent_toQCoh_fppf_kernel {F G : Coh X} (φ : F ⟶ G) :
    AlgebraicStack.IsCoherent
      ((QCoh.inclusion X).obj
        ((LQCohFbc.toQCoh X).obj (QCoh.kernelLQCohFbc (Coh.toQCoh.map φ)))) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
