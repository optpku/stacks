/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import stacks_project.Chap96.Lemma_96_15_1_Abelian
public import stacks_project.Chap103.Lemma_103_10_2
public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc
import StacksCheckRecall

/-!
# Remark 103.10.5

On an algebraic stack, `QCoh` is abelian and its inclusion into `Mod` is right
exact but not exact. Cokernels and images of a map `φ` of quasi-coherent
modules agree in `Mod` and in `QCoh`, while the kernel computed in `Mod` lies
in `LQCoh^{fbc}` and `Q` of that kernel is the kernel in `QCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/- Remark 103.10.5 (1): the category `QCoh(𝒪_𝒳)` of an algebraic stack is abelian. -/
@[stacks 0GQL] #check abelian

/- Remark 103.10.5 (2): the inclusion `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` preserves finite
colimits, hence is right exact. -/
@[stacks 0GQL] #check inclusion_preservesFiniteColimits

/-- Remark 103.10.5 (3): the inclusion `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` is not exact in
general. -/
@[stacks 0GQL]
theorem inclusion_not_exact_in_general :
    ¬ ∀ (S : Scheme.{u}) (X : GroupoidsOver S) [AlgebraicStack X],
      exactFunctor (QCoh X) (RingedSite.ModuleCat.{u} (fppfRingedSite X))
        (inclusion X) :=
  sorry

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- Remark 103.10.5 (4): the cokernel of a map of quasi-coherent modules, computed
in `Mod(𝒪_𝒳)`, is the image of the `QCoh` cokernel under inclusion. -/
@[stacks 0GQL]
def inclusion_cokernelIso {F G : QCoh X} (φ : F ⟶ G) :
    cokernel ((inclusion X).map φ) ≅ (inclusion X).obj (cokernel φ) :=
  (PreservesCokernel.iso (inclusion X) φ).symm

/-- `inclusion_cokernelIso` is the inverse of `PreservesCokernel.iso`. -/
theorem inclusion_cokernelIso_eq {F G : QCoh X} (φ : F ⟶ G) :
    inclusion_cokernelIso φ = (PreservesCokernel.iso (inclusion X) φ).symm :=
  sorry

/-- The cokernel of a map of quasi-coherent modules, computed in `Mod(𝒪_𝒳)`, is
quasi-coherent. -/
instance isQuasicoherent_cokernel {F G : QCoh X} (φ : F ⟶ G) :
    (cokernel ((inclusion X).map φ)).IsQuasicoherent :=
  sorry

/-- Comparison from the included `QCoh` image of `φ` to the image of `φ` computed
in `Mod(𝒪_𝒳)`. -/
def inclusion_imageComparison {F G : QCoh X} (φ : F ⟶ G) :
    (inclusion X).obj (Abelian.image φ) ⟶ Abelian.image ((inclusion X).map φ) :=
  kernelComparison (cokernel.π φ) (inclusion X) ≫
    (kernel.mapIso ((inclusion X).map (cokernel.π φ))
      (cokernel.π ((inclusion X).map φ)) (Iso.refl _)
      (PreservesCokernel.iso (inclusion X) φ)
      (PreservesCokernel.π_iso_hom (inclusion X) φ)).hom

/-- Remark 103.10.5 (5): the image of a map of quasi-coherent modules, computed
in `Mod(𝒪_𝒳)`, agrees with the image in `QCoh(𝒪_𝒳)`. -/
@[stacks 0GQL]
instance inclusion_imageComparison_isIso {F G : QCoh X} (φ : F ⟶ G) :
    IsIso (inclusion_imageComparison φ) :=
  sorry

/-- The image of a map of quasi-coherent modules, computed in `Mod(𝒪_𝒳)`, is
quasi-coherent. -/
instance isQuasicoherent_image {F G : QCoh X} (φ : F ⟶ G) :
    (Abelian.image ((inclusion X).map φ)).IsQuasicoherent :=
  sorry

/-- Remark 103.10.5 (6): the kernel of a map of quasi-coherent modules, computed
in `Mod(𝒪_𝒳)`, lies in `LQCoh^{fbc}(𝒪_𝒳)`. -/
@[stacks 0GQL]
theorem kernel_mem_lqcohFbc {F G : QCoh X} (φ : F ⟶ G) :
    FppfModules.lqcohFbc X (kernel ((inclusion X).map φ)) :=
  sorry

/-- Remark 103.10.5 (7): `Q` of the kernel of `φ` in `LQCoh^{fbc}` is the kernel
of `φ` in `QCoh`. -/
@[stacks 0GQL]
def kernelIso_toQCoh {F G : QCoh X} (φ : F ⟶ G) :
    kernel φ ≅ (LQCohFbc.toQCoh X).obj (kernel ((toLQCohFbc X).map φ)) :=
  (PreservesKernel.iso (LQCohFbc.toQCoh X) ((toLQCohFbc X).map φ) ≪≫
    kernel.mapIso ((toLQCohFbc X ⋙ LQCohFbc.toQCoh X).map φ) φ
      ((toLQCohFbc_comp_toQCoh X).app F) ((toLQCohFbc_comp_toQCoh X).app G)
      ((toLQCohFbc_comp_toQCoh X).hom.naturality φ)).symm

/-- `kernelIso_toQCoh` is `PreservesKernel.iso` of `toQCoh` transported along
`toLQCohFbc ⋙ toQCoh ≅ 𝟭`. -/
theorem kernelIso_toQCoh_eq {F G : QCoh X} (φ : F ⟶ G) :
    kernelIso_toQCoh φ =
      (PreservesKernel.iso (LQCohFbc.toQCoh X) ((toLQCohFbc X).map φ) ≪≫
        kernel.mapIso ((toLQCohFbc X ⋙ LQCohFbc.toQCoh X).map φ) φ
          ((toLQCohFbc_comp_toQCoh X).app F) ((toLQCohFbc_comp_toQCoh X).app G)
          ((toLQCohFbc_comp_toQCoh X).hom.naturality φ)).symm :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
