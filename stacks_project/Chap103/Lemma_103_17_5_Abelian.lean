module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import stacks_project.Chap103.Definition_103_17_2_Coh
public import stacks_project.Chap103.Remark_103_10_5

/-!
# Abelian structure on coherent modules of a locally Noetherian algebraic stack

On a locally Noetherian algebraic stack, `Coh(𝒪_X)` is abelian. Cokernels and
images of a map of coherent modules agree with those computed in `Mod`, while
the kernel computed in `Mod` lies in `LQCoh^{fbc}` and `Q` of that kernel is
the kernel in `Coh`. The inclusion `Coh ⟶ QCoh` is exact.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- Inclusion of coherent `𝒪_X`-modules into quasi-coherent `𝒪_X`-modules, as
the lift of `Coh.inclusion` through `quasiCoherentModuleProperty`. -/
def Coh.qCohLift : Coh X ⥤ QCoh X :=
  (quasiCoherentModuleProperty X).lift (Coh.inclusion X) (fun _ ↦ sorry)

/-- The zero sheaf of modules is coherent on a locally Noetherian algebraic
stack. -/
instance coherentModuleProperty.containsZero :
    (coherentModuleProperty X).ContainsZero :=
  sorry

/-- Coherent modules on a locally Noetherian algebraic stack are closed under
cokernels in `Mod(𝒪_X)`. -/
instance coherentModuleProperty.isClosedUnderCokernels :
    (coherentModuleProperty X).IsClosedUnderCokernels :=
  sorry

namespace Coh

/-- The category `Coh(𝒪_X)` of a locally Noetherian algebraic stack is abelian. -/
instance abelian : Abelian (Coh X) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

end Coh

/-- The cokernel of a map of coherent `𝒪_X`-modules, computed in `Mod(𝒪_X)`, is
coherent. -/
instance isCoherent_cokernel {F G : SheafOfModules.{u} (structureSheaf X)}
    [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G] (φ : F ⟶ G) :
    AlgebraicStack.IsCoherent (cokernel φ) :=
  sorry

/-- The image of a map of coherent `𝒪_X`-modules, computed in `Mod(𝒪_X)`, is
coherent. -/
instance isCoherent_image {F G : SheafOfModules.{u} (structureSheaf X)}
    [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G] (φ : F ⟶ G) :
    AlgebraicStack.IsCoherent (Abelian.image φ) :=
  sorry

namespace Coh

/-- The inclusion `Coh(𝒪_X) ⟶ Mod(𝒪_X)` preserves finite colimits. -/
instance inclusion_preservesFiniteColimits :
    PreservesFiniteColimits (inclusion X) :=
  sorry

/-- The cokernel of a map of coherent modules, computed in `Mod(𝒪_X)`, is the
image of the `Coh` cokernel under inclusion. -/
def inclusion_cokernelIso {F G : Coh X} (φ : F ⟶ G) :
    cokernel ((inclusion X).map φ) ≅ (inclusion X).obj (cokernel φ) :=
  (PreservesCokernel.iso (inclusion X) φ).symm

/-- `inclusion_cokernelIso` is the inverse of `PreservesCokernel.iso`. -/
theorem inclusion_cokernelIso_eq {F G : Coh X} (φ : F ⟶ G) :
    inclusion_cokernelIso φ = (PreservesCokernel.iso (inclusion X) φ).symm :=
  sorry

end Coh

/-- The kernel of a map of coherent `𝒪_X`-modules, computed in `Mod(𝒪_X)`, lies
in `LQCoh^{fbc}(𝒪_X)`. -/
theorem kernel_mem_lqcohFbc {F G : Coh X} (φ : F ⟶ G) :
    FppfModules.lqcohFbc X (kernel ((Coh.inclusion X).map φ)) :=
  sorry

/-- `Q` of the kernel of a map of coherent modules, equivalently the kernel
computed in `QCoh`, is coherent. -/
instance isCoherent_toQCoh_kernel {F G : Coh X} (φ : F ⟶ G) :
    AlgebraicStack.IsCoherent
      ((QCoh.inclusion X).obj (kernel (Coh.qCohLift.map φ))) :=
  sorry

namespace Coh

/-- The inclusion `Coh(𝒪_X) ⟶ QCoh(𝒪_X)` preserves zero morphisms. -/
instance qCohLift_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (qCohLift : Coh X ⥤ QCoh X) :=
  sorry

/-- The inclusion `Coh(𝒪_X) ⟶ QCoh(𝒪_X)` preserves finite limits. -/
instance qCohLift_preservesFiniteLimits :
    PreservesFiniteLimits (qCohLift : Coh X ⥤ QCoh X) :=
  sorry

/-- The inclusion `Coh(𝒪_X) ⟶ QCoh(𝒪_X)` preserves finite colimits. -/
instance qCohLift_preservesFiniteColimits :
    PreservesFiniteColimits (qCohLift : Coh X ⥤ QCoh X) :=
  sorry

/-- `Q` of the kernel of `φ` in `LQCoh^{fbc}` is the image of the `Coh` kernel
under inclusion into `QCoh`. -/
def kernelIso_toQCoh {F G : Coh X} (φ : F ⟶ G) :
    qCohLift.obj (kernel φ) ≅
      (LQCohFbc.toQCoh X).obj
        (kernel ((QCoh.toLQCohFbc X).map (qCohLift.map φ))) :=
  PreservesKernel.iso qCohLift φ ≪≫ QCoh.kernelIso_toQCoh (qCohLift.map φ)

/-- `kernelIso_toQCoh` is `PreservesKernel.iso` of `qCohLift` composed with the
`QCoh` kernel identification of Remark 103.10.5. -/
theorem kernelIso_toQCoh_eq {F G : Coh X} (φ : F ⟶ G) :
    kernelIso_toQCoh φ =
      PreservesKernel.iso qCohLift φ ≪≫
        QCoh.kernelIso_toQCoh (qCohLift.map φ) :=
  sorry

/-- The inclusion functor `Coh(𝒪_X) ⟶ QCoh(𝒪_X)` is exact. -/
theorem qCohLift_exact : exactFunctor (Coh X) (QCoh X) qCohLift :=
  sorry

end Coh

end AlgebraicGeometry.AlgebraicStack
