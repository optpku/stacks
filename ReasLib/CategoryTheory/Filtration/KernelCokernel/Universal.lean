module

public import ReasLib.CategoryTheory.Filtration.KernelCokernel

/-!
# Universal Properties of Filtered Kernels and Cokernels

The induced filtration on a kernel and the quotient filtration on a cokernel retain the expected
universal properties in the category of filtered objects. This file exposes the canonical lifts,
descents, computation rules, and selected limit and colimit models with no abelian hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

open FilteredObject

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FilteredObject C}

section Cokernel

variable [HasZeroMorphisms C] [HasImages C] [HasCokernels C]

/-- The ambient morphism underlying descent through a filtered cokernel. -/
noncomputable abbrev cokernelDescHom (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) :
    (cokernel f).obj ⟶ Z.obj :=
  Limits.cokernel.desc f.hom g.hom (hom_comp_eq_zero f g hfg)

/-- Descent through the ambient cokernel preserves the quotient filtration. -/
theorem cokernelDesc_preserves (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0)
    (p : ℤ) :
    (Z.filtration p).Factors
      (((cokernel f).filtration p).arrow ≫ cokernelDescHom f g hfg) := sorry

/-- The canonical filtered descent of a morphism annihilating `f`. -/
noncomputable def cokernelDesc (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) :
    cokernel f ⟶ Z where
  hom := cokernelDescHom f g hfg
  preserves := cokernelDesc_preserves f g hfg

/-- The underlying map of the filtered cokernel descent is the ambient cokernel descent. -/
@[simp]
theorem cokernelDesc_hom (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) :
    (cokernelDesc f g hfg).hom = cokernelDescHom f g hfg := sorry

/-- Composing the filtered cokernel projection with its canonical descent recovers the original
morphism. -/
@[reassoc (attr := simp)]
theorem toCokernel_cokernelDesc (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) :
    toCokernel f ≫ cokernelDesc f g hfg = g := sorry

/-- Postcomposing a filtered cokernel descent agrees with the descent of the postcomposite. -/
theorem cokernelDesc_comp {W : FilteredObject C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) (h : Z ⟶ W)
    (hfgh : f ≫ (g ≫ h) = 0) :
    cokernelDesc f g hfg ≫ h = cokernelDesc f (g ≫ h) hfgh := sorry

/-- A morphism out of a filtered cokernel is determined by its composite with the projection. -/
theorem cokernelDesc_unique (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0)
    (k : cokernel f ⟶ Z) (hk : toCokernel f ≫ k = g) :
    k = cokernelDesc f g hfg := sorry

/-- Two morphisms out of a filtered cokernel agree when they agree after the projection. -/
theorem cokernel_hom_ext (f : X ⟶ Y) {g h : cokernel f ⟶ Z}
    (w : toCokernel f ≫ g = toCokernel f ≫ h) : g = h := sorry

/-- The filtered cokernel projection exhibits the quotient-filtered cokernel as a categorical
cokernel. -/
noncomputable def toCokernelIsColimit (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ (toCokernel f) (comp_toCokernel f)) := sorry

/-- The chosen universal cokernel descent computes to `cokernelDesc`. -/
@[simp]
theorem toCokernelIsColimit_desc (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) :
    (toCokernelIsColimit f).desc (CokernelCofork.ofπ g hfg) =
      cokernelDesc f g hfg := sorry

/-- The filtered cokernel projection is epic. -/
instance toCokernel_epi (f : X ⟶ Y) : Epi (toCokernel f) := sorry

end Cokernel

section Kernel

variable [HasZeroMorphisms C] [HasKernels C]

/-- A morphism annihilating `f` factors through the ambient kernel subobject. -/
theorem kernelLift_factors (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0) :
    (kernelSubobject f.hom).Factors g.hom := sorry

section

variable [HasPullbacks C]

/-- The ambient morphism underlying the lift into a filtered kernel. -/
noncomputable abbrev kernelLiftHom (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0) :
    Z.obj ⟶ (kernel f).obj :=
  (kernelSubobject f.hom).factorThru g.hom (kernelLift_factors f g hgf)

/-- The ambient kernel lift preserves the induced filtration. -/
theorem kernelLift_preserves (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0)
    (p : ℤ) :
    ((kernel f).filtration p).Factors
      ((Z.filtration p).arrow ≫ kernelLiftHom f g hgf) := sorry

/-- The canonical filtered lift of a morphism annihilated by `f`. -/
noncomputable def kernelLift (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0) :
    Z ⟶ kernel f where
  hom := kernelLiftHom f g hgf
  preserves := kernelLift_preserves f g hgf

/-- The underlying map of the filtered kernel lift is the ambient kernel-subobject lift. -/
@[simp]
theorem kernelLift_hom (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0) :
    (kernelLift f g hgf).hom = kernelLiftHom f g hgf := sorry

/-- Composing the canonical filtered kernel lift with the kernel inclusion recovers the original
morphism. -/
@[reassoc (attr := simp)]
theorem kernelLift_kernelι (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0) :
    kernelLift f g hgf ≫ kernelι f = g := sorry

/-- Precomposing a filtered kernel lift agrees with the lift of the precomposite. -/
theorem comp_kernelLift {W : FilteredObject C}
    (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0) (h : W ⟶ Z)
    (hhgf : (h ≫ g) ≫ f = 0) :
    h ≫ kernelLift f g hgf = kernelLift f (h ≫ g) hhgf := sorry

/-- A morphism into a filtered kernel is determined by its composite with the inclusion. -/
theorem kernelLift_unique (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0)
    (k : Z ⟶ kernel f) (hk : k ≫ kernelι f = g) :
    k = kernelLift f g hgf := sorry

/-- Two morphisms into a filtered kernel agree when they agree after the inclusion. -/
theorem kernel_hom_ext (f : X ⟶ Y) {g h : Z ⟶ kernel f}
    (w : g ≫ kernelι f = h ≫ kernelι f) : g = h := sorry

/-- The filtered kernel inclusion exhibits the induced filtered kernel as a categorical kernel. -/
noncomputable def kernelιIsLimit (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kernelι f) (kernelι_comp f)) := sorry

/-- The chosen universal kernel lift computes to `kernelLift`. -/
@[simp]
theorem kernelιIsLimit_lift (f : X ⟶ Y) (g : Z ⟶ X) (hgf : g ≫ f = 0) :
    (kernelιIsLimit f).lift (KernelFork.ofι g hgf) = kernelLift f g hgf := sorry

/-- The filtered kernel inclusion is monic. -/
instance kernelι_mono (f : X ⟶ Y) : Mono (kernelι f) := sorry

end

end Kernel

end CategoryTheory.FilteredObject.Hom
