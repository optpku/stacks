/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_3_2_Category
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

namespace FGTorsionFreeModuleCat

variable {N M : FGTorsionFreeModuleCat.{v} R}

/-- The kernel object of a morphism in `FGTorsionFreeModuleCat`, as the ordinary module kernel. -/
def kernelObj (f : N ⟶ M) : FGTorsionFreeModuleCat.{v} R where
  obj := ModuleCat.of R (LinearMap.ker f.hom.hom)
  property := sorry

/-- The kernel inclusion of a morphism in `FGTorsionFreeModuleCat`. -/
def kernelι (f : N ⟶ M) : kernelObj f ⟶ N :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker f.hom.hom).subtype)

/-- The unique lift of a morphism through the kernel inclusion, via `LinearMap.codRestrict`. -/
def kernelι_lift {W : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : W ⟶ N)
    (hg : g ≫ f = 0) : W ⟶ kernelObj f :=
  ObjectProperty.homMk
    (ConcreteCategory.ofHom
      (LinearMap.codRestrict (LinearMap.ker f.hom.hom) g.hom.hom (fun _ ↦ sorry)))

/-- The kernel inclusion composes to zero. -/
theorem kernel_condition (f : N ⟶ M) : kernelι f ≫ f = 0 :=
  sorry

/-- The named kernel inclusion is a categorical kernel. -/
noncomputable def kernelι_isKernel (f : N ⟶ M) :
    IsLimit (KernelFork.ofι (kernelι f) (kernel_condition f)) :=
  KernelFork.IsLimit.ofι (kernelι f) (kernel_condition f)
    (fun {W'} g' hg' ↦ kernelι_lift f g' hg')
    (fun {W'} g' hg' ↦ sorry)
    (fun {W'} g' hg' m hm ↦ sorry)

/-- The cokernel object of a morphism in `FGTorsionFreeModuleCat`, as the torsion-free quotient of
the module cokernel. -/
def cokernelObj (f : N ⟶ M) : FGTorsionFreeModuleCat.{v} R where
  obj := ModuleCat.of R
    ((M.obj ⧸ LinearMap.range f.hom.hom) ⧸
      Submodule.torsion R (M.obj ⧸ LinearMap.range f.hom.hom))
  property := sorry

/-- The cokernel projection of a morphism in `FGTorsionFreeModuleCat`. -/
def cokernelπ (f : N ⟶ M) : M ⟶ cokernelObj f :=
  ObjectProperty.homMk
    (ModuleCat.ofHom
      ((Submodule.torsion R (M.obj ⧸ LinearMap.range f.hom.hom)).mkQ.comp
        (LinearMap.range f.hom.hom).mkQ))

/-- The unique descent of a morphism through the cokernel projection, via successive
`Submodule.liftQ`. -/
def cokernelπ_desc {P : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : M ⟶ P)
    (hg : f ≫ g = 0) : cokernelObj f ⟶ P :=
  ObjectProperty.homMk
    (ConcreteCategory.ofHom
      ((Submodule.torsion R (M.obj ⧸ LinearMap.range f.hom.hom)).liftQ
        ((LinearMap.range f.hom.hom).liftQ g.hom.hom sorry) sorry))

/-- The cokernel projection composes to zero. -/
theorem cokernel_condition (f : N ⟶ M) : f ≫ cokernelπ f = 0 :=
  sorry

/-- The named cokernel projection is a categorical cokernel. -/
noncomputable def cokernelπ_isCokernel (f : N ⟶ M) :
    IsColimit (CokernelCofork.ofπ (cokernelπ f) (cokernel_condition f)) :=
  CokernelCofork.IsColimit.ofπ (cokernelπ f) (cokernel_condition f)
    (fun {Z'} g' hg' ↦ cokernelπ_desc f g' hg')
    (fun {Z'} g' hg' ↦ sorry)
    (fun {Z'} g' hg' m hm ↦ sorry)

variable (R) in
/-- The ambient category `ModuleCat R` has kernels given by ordinary module kernels. -/
instance instHasKernelsModuleCat : HasKernels (ModuleCat.{v} R) :=
  ModuleCat.hasKernels_moduleCat

variable (R) in
/-- Kernels of morphisms of finitely generated torsion-free modules remain finitely generated and
torsion-free. -/
instance instIsClosedUnderKernels :
    (ModuleCat.isFGTorsionFree.{v} R).IsClosedUnderKernels :=
  sorry

/-- The named kernel object is the categorical kernel. -/
noncomputable def kernelObjIsoKernel (f : N ⟶ M) : kernelObj f ≅ kernel f :=
  (limit.isoLimitCone
    ⟨KernelFork.ofι (kernelι f) (kernel_condition f), kernelι_isKernel f⟩).symm

variable (R) in
/-- Over a Noetherian domain, finitely generated torsion-free modules have cokernels, created as
the torsion-free quotient of the module cokernel. -/
instance instHasCokernels : HasCokernels (FGTorsionFreeModuleCat.{v} R) where
  has_colimit f :=
    HasColimit.mk
      ⟨CokernelCofork.ofπ (cokernelπ f) (cokernel_condition f), cokernelπ_isCokernel f⟩

/-- The named cokernel object is the categorical cokernel. -/
noncomputable def cokernelIsoCokernelObj (f : N ⟶ M) : cokernel f ≅ cokernelObj f :=
  colimit.isoColimitCocone
    ⟨CokernelCofork.ofπ (cokernelπ f) (cokernel_condition f), cokernelπ_isCokernel f⟩

end FGTorsionFreeModuleCat
