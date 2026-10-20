module

public import ReasLib.Algebra.Category.FGTorsionFreeModuleCat.Basic
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

/-- The ordinary linear-map kernel is finitely generated and torsion-free. -/
theorem kernelObj_property (f : N ⟶ M) :
    ModuleCat.isFGTorsionFree R (ModuleCat.of R (LinearMap.ker f.hom.hom)) :=
  sorry

/-- The kernel object is the ordinary linear-map kernel. -/
def kernelObj (f : N ⟶ M) : FGTorsionFreeModuleCat.{v} R where
  obj := ModuleCat.of R (LinearMap.ker f.hom.hom)
  property := kernelObj_property f

/-- The kernel inclusion is the submodule inclusion. -/
def kernelι (f : N ⟶ M) : kernelObj f ⟶ N :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker f.hom.hom).subtype)

/-- A linear map annihilated by a morphism takes values in its linear-map kernel. -/
theorem kernel_lift_mem {W : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : W ⟶ N)
    (hg : g ≫ f = 0) (element : W) : g.hom.hom element ∈ LinearMap.ker f.hom.hom :=
  sorry

/-- The lift through the kernel inclusion is codomain restriction to the kernel. -/
def kernelι_lift {W : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : W ⟶ N)
    (hg : g ≫ f = 0) : W ⟶ kernelObj f :=
  ObjectProperty.homMk
    (ConcreteCategory.ofHom
      (LinearMap.codRestrict (LinearMap.ker f.hom.hom) g.hom.hom
        (kernel_lift_mem f g hg)))

/-- The underlying value of the kernel lift is the original linear-map value. -/
theorem kernelι_lift_apply {W : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : W ⟶ N)
    (hg : g ≫ f = 0) (element : W) :
    (kernelι_lift f g hg).hom.hom element =
      ⟨g.hom.hom element, kernel_lift_mem f g hg element⟩ :=
  rfl

/-- The kernel inclusion composes to zero. -/
theorem kernel_condition (f : N ⟶ M) : kernelι f ≫ f = 0 :=
  sorry

/-- The kernel lift factors the original morphism through the inclusion. -/
theorem kernelι_lift_fac {W : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : W ⟶ N)
    (hg : g ≫ f = 0) : kernelι_lift f g hg ≫ kernelι f = g :=
  sorry

/-- A morphism into the kernel with the prescribed composite is the kernel lift. -/
theorem kernelι_lift_unique {W : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : W ⟶ N)
    (hg : g ≫ f = 0) (lift : W ⟶ kernelObj f) (hlift : lift ≫ kernelι f = g) :
    lift = kernelι_lift f g hg :=
  sorry

/-- The kernel inclusion has the categorical kernel universal property. -/
noncomputable def kernelι_isKernel (f : N ⟶ M) :
    IsLimit (KernelFork.ofι (kernelι f) (kernel_condition f)) :=
  KernelFork.IsLimit.ofι (kernelι f) (kernel_condition f)
    (fun {W'} g' hg' ↦ kernelι_lift f g' hg')
    (fun {W'} g' hg' ↦ kernelι_lift_fac f g' hg')
    (fun {W'} g' hg' lift hlift ↦ kernelι_lift_unique f g' hg' lift hlift)

/-- Quotienting the module cokernel by its torsion gives a finitely generated torsion-free module. -/
theorem cokernelObj_property (f : N ⟶ M) :
    ModuleCat.isFGTorsionFree R (ModuleCat.of R
      ((M.obj ⧸ LinearMap.range f.hom.hom) ⧸
        Submodule.torsion R (M.obj ⧸ LinearMap.range f.hom.hom))) :=
  sorry

/-- The cokernel object is the quotient of the ordinary module cokernel by its torsion. -/
def cokernelObj (f : N ⟶ M) : FGTorsionFreeModuleCat.{v} R where
  obj := ModuleCat.of R
    ((M.obj ⧸ LinearMap.range f.hom.hom) ⧸
      Submodule.torsion R (M.obj ⧸ LinearMap.range f.hom.hom))
  property := cokernelObj_property f

/-- The cokernel projection is the composite of the range quotient and the torsion quotient. -/
def cokernelπ (f : N ⟶ M) : M ⟶ cokernelObj f :=
  ObjectProperty.homMk
    (ModuleCat.ofHom
      ((Submodule.torsion R (M.obj ⧸ LinearMap.range f.hom.hom)).mkQ.comp
        (LinearMap.range f.hom.hom).mkQ))

/-- A morphism annihilating a linear map vanishes on its range. -/
theorem cokernel_desc_range_le_ker {P : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M)
    (g : M ⟶ P) (hg : f ≫ g = 0) : LinearMap.range f.hom.hom ≤ LinearMap.ker g.hom.hom :=
  sorry

/-- The descent to the module cokernel vanishes on torsion when its target is torsion-free. -/
theorem cokernel_desc_torsion_le_ker {P : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M)
    (g : M ⟶ P) (hg : f ≫ g = 0) :
    Submodule.torsion R (M.obj ⧸ LinearMap.range f.hom.hom) ≤
      LinearMap.ker ((LinearMap.range f.hom.hom).liftQ g.hom.hom
        (cokernel_desc_range_le_ker f g hg)) :=
  sorry

/-- The descent through the cokernel projection is successive descent through the two quotients. -/
def cokernelπ_desc {P : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : M ⟶ P)
    (hg : f ≫ g = 0) : cokernelObj f ⟶ P :=
  ObjectProperty.homMk
    (ConcreteCategory.ofHom
      ((Submodule.torsion R (M.obj ⧸ LinearMap.range f.hom.hom)).liftQ
        ((LinearMap.range f.hom.hom).liftQ g.hom.hom
          (cokernel_desc_range_le_ker f g hg)) (cokernel_desc_torsion_le_ker f g hg)))

/-- The cokernel descent sends the double quotient class of an element to its original image. -/
theorem cokernelπ_desc_apply {P : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : M ⟶ P)
    (hg : f ≫ g = 0) (element : M) :
    (cokernelπ_desc f g hg).hom.hom ((cokernelπ f).hom.hom element) = g.hom.hom element :=
  rfl

/-- The cokernel projection composes to zero. -/
theorem cokernel_condition (f : N ⟶ M) : f ≫ cokernelπ f = 0 :=
  sorry

/-- The cokernel descent factors the original morphism through the projection. -/
theorem cokernelπ_desc_fac {P : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : M ⟶ P)
    (hg : f ≫ g = 0) : cokernelπ f ≫ cokernelπ_desc f g hg = g :=
  sorry

/-- A morphism out of the cokernel with the prescribed composite is the cokernel descent. -/
theorem cokernelπ_desc_unique {P : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M) (g : M ⟶ P)
    (hg : f ≫ g = 0) (desc : cokernelObj f ⟶ P) (hdesc : cokernelπ f ≫ desc = g) :
    desc = cokernelπ_desc f g hg :=
  sorry

/-- The cokernel projection has the categorical cokernel universal property. -/
noncomputable def cokernelπ_isCokernel (f : N ⟶ M) :
    IsColimit (CokernelCofork.ofπ (cokernelπ f) (cokernel_condition f)) :=
  CokernelCofork.IsColimit.ofπ (cokernelπ f) (cokernel_condition f)
    (fun {Z'} g' hg' ↦ cokernelπ_desc f g' hg')
    (fun {Z'} g' hg' ↦ cokernelπ_desc_fac f g' hg')
    (fun {Z'} g' hg' desc hdesc ↦ cokernelπ_desc_unique f g' hg' desc hdesc)

variable (R) in
/-- Kernels of finitely generated torsion-free modules over a Noetherian domain are finitely
 generated and torsion-free. -/
instance instIsClosedUnderKernels :
    (ModuleCat.isFGTorsionFree.{v} R).IsClosedUnderKernels :=
  sorry

variable (R) in
/-- Finitely generated torsion-free modules over a Noetherian domain have kernels given by
 ordinary linear-map kernels. -/
instance instHasKernels : HasKernels (FGTorsionFreeModuleCat.{v} R) where
  has_limit f :=
    HasLimit.mk
      ⟨KernelFork.ofι (kernelι f) (kernel_condition f), kernelι_isKernel f⟩

/-- The ordinary linear-map kernel is canonically isomorphic to the categorical kernel. -/
noncomputable def kernelObjIsoKernel (f : N ⟶ M) : kernelObj f ≅ kernel f :=
  (limit.isoLimitCone
    ⟨KernelFork.ofι (kernelι f) (kernel_condition f), kernelι_isKernel f⟩).symm

/-- The canonical kernel isomorphism identifies the categorical inclusion with the submodule inclusion. -/
theorem kernelObjIsoKernel_hom_ι (f : N ⟶ M) :
    (kernelObjIsoKernel f).hom ≫ kernel.ι f = kernelι f :=
  limit.isoLimitCone_inv_π
    ⟨KernelFork.ofι (kernelι f) (kernel_condition f), kernelι_isKernel f⟩
    WalkingParallelPair.zero

variable (R) in
/-- Finitely generated torsion-free modules over a Noetherian domain have cokernels given by
 torsion-free quotients of module cokernels. -/
instance instHasCokernels : HasCokernels (FGTorsionFreeModuleCat.{v} R) where
  has_colimit f :=
    HasColimit.mk
      ⟨CokernelCofork.ofπ (cokernelπ f) (cokernel_condition f), cokernelπ_isCokernel f⟩

/-- The categorical cokernel is canonically isomorphic to the torsion-free double quotient. -/
noncomputable def cokernelIsoCokernelObj (f : N ⟶ M) : cokernel f ≅ cokernelObj f :=
  colimit.isoColimitCocone
    ⟨CokernelCofork.ofπ (cokernelπ f) (cokernel_condition f), cokernelπ_isCokernel f⟩

/-- The canonical cokernel isomorphism identifies the categorical projection with the double quotient map. -/
theorem cokernelIsoCokernelObj_π_hom (f : N ⟶ M) :
    cokernel.π f ≫ (cokernelIsoCokernelObj f).hom = cokernelπ f :=
  colimit.isoColimitCocone_ι_hom
    ⟨CokernelCofork.ofπ (cokernelπ f) (cokernel_condition f), cokernelπ_isCokernel f⟩
    WalkingParallelPair.one

end FGTorsionFreeModuleCat
