/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Comparison
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular

/-!
# Tensor products of meromorphic sections on algebraic spaces

Meromorphic sections of an `𝒪_X`-module are global sections of `𝒦_X(F)`. Their
tensor is the pure `𝒦_X`-tensor of those sections, transported to `𝒦_X(L ⊗ N)`
by sheafifying the objectwise localization bilinear map
`(m / s, n / t) ↦ (m ⊗ n) / (s * t)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open SheafOfModules SheafOfModules.RingedSite
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

private theorem meromorphicSectionLocalizedTensor_right_wd (L N : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ)
    (p : (liftModule L).val.obj U × (regularStructureSections X).obj U)
    (q q' : (liftModule N).val.obj U × (regularStructureSections X).obj U)
    (h : q ≈ q') :
    LocalizedModule.mk (RelativeProj.liftModuleTensorSection L N U p.1 q.1) (p.2 * q.2) =
      LocalizedModule.mk (RelativeProj.liftModuleTensorSection L N U p.1 q'.1)
        (p.2 * q'.2) := sorry

private theorem meromorphicSectionLocalizedTensor_left_wd (L N : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ)
    (y : LocalizedModule ((regularStructureSections X).obj U) ((liftModule N).val.obj U))
    (p p' : (liftModule L).val.obj U × (regularStructureSections X).obj U)
    (h : p ≈ p') :
    LocalizedModule.liftOn y
        (fun q ↦ LocalizedModule.mk
          (RelativeProj.liftModuleTensorSection L N U p.1 q.1) (p.2 * q.2))
        (meromorphicSectionLocalizedTensor_right_wd L N U p) =
      LocalizedModule.liftOn y
        (fun q ↦ LocalizedModule.mk
          (RelativeProj.liftModuleTensorSection L N U p'.1 q.1) (p'.2 * q.2))
        (meromorphicSectionLocalizedTensor_right_wd L N U p') := sorry

/-- The tensor of localized module sections sends `(m/a, n/b)` to `(m ⊗ n)/(ab)`. -/
def meromorphicSectionLocalizedTensor (L N : X.Modules)
    {U : (smallEtaleSite X)ᵒᵖ}
    (x : LocalizedModule ((regularStructureSections X).obj U) ((liftModule L).val.obj U))
    (y : LocalizedModule ((regularStructureSections X).obj U) ((liftModule N).val.obj U)) :
    LocalizedModule ((regularStructureSections X).obj U) ((liftModule (L ⊗ N)).val.obj U) :=
  LocalizedModule.liftOn x
    (fun p ↦ LocalizedModule.liftOn y
      (fun q ↦ LocalizedModule.mk
        (RelativeProj.liftModuleTensorSection L N U p.1 q.1) (p.2 * q.2))
      (by exact meromorphicSectionLocalizedTensor_right_wd L N U p))
    (by exact meromorphicSectionLocalizedTensor_left_wd L N U y)

/-- Tensoring fractions multiplies their denominators and tensors their numerators. -/
theorem meromorphicSectionLocalizedTensor_mk (L N : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ)
    (m : (liftModule L).val.obj U) (n : (liftModule N).val.obj U)
    (a b : (regularStructureSections X).obj U) :
    meromorphicSectionLocalizedTensor L N (LocalizedModule.mk m a) (LocalizedModule.mk n b) =
      LocalizedModule.mk (RelativeProj.liftModuleTensorSection L N U m n) (a * b) := by
  simp only [meromorphicSectionLocalizedTensor, LocalizedModule.liftOn_mk]

private theorem meromorphicSectionLocalizedTensor_add_right (L N : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : (meromorphicSectionPresheaf X L).obj U) (y z : (meromorphicSectionPresheaf X N).obj U) :
    meromorphicSectionLocalizedTensor L N x (y + z) =
      meromorphicSectionLocalizedTensor L N x y + meromorphicSectionLocalizedTensor L N x z := sorry

private theorem meromorphicSectionLocalizedTensor_smul_right (L N : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ)
    (r : (regularStructureSections X).localizationPresheaf.obj U) (x : (meromorphicSectionPresheaf X L).obj U) (y : (meromorphicSectionPresheaf X N).obj U) :
    meromorphicSectionLocalizedTensor L N x (r • y) =
      r • meromorphicSectionLocalizedTensor L N x y := sorry

private theorem meromorphicSectionLocalizedTensor_add_left (L N : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x y : (meromorphicSectionPresheaf X L).obj U) (z : (meromorphicSectionPresheaf X N).obj U) :
    meromorphicSectionLocalizedTensor L N (x + y) z =
      meromorphicSectionLocalizedTensor L N x z + meromorphicSectionLocalizedTensor L N y z := sorry

private theorem meromorphicSectionLocalizedTensor_smul_left (L N : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ)
    (r : (regularStructureSections X).localizationPresheaf.obj U) (x : (meromorphicSectionPresheaf X L).obj U) (y : (meromorphicSectionPresheaf X N).obj U) :
    meromorphicSectionLocalizedTensor L N (r • x) y =
      r • meromorphicSectionLocalizedTensor L N x y := sorry

private theorem meromorphicSectionPresheafTensorBilinear_naturality (L N : X.Modules)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (x : (meromorphicSectionPresheaf X L).obj U)
    (y : (meromorphicSectionPresheaf X N).obj U) :
    (meromorphicSectionPresheaf X (L ⊗ N)).map i
        (meromorphicSectionLocalizedTensor L N x y) =
      meromorphicSectionLocalizedTensor L N
        ((meromorphicSectionPresheaf X L).map i x)
        ((meromorphicSectionPresheaf X N).map i y) := sorry

/-- Compatible bilinear map of meromorphic-section presheaves. -/
def meromorphicSectionPresheafTensorBilinear (L N : X.Modules) :
    PresheafOfModules.BilinearMap
      (regularStructureSections X).localizationPresheaf
      (meromorphicSectionPresheaf X L)
      (meromorphicSectionPresheaf X N)
      (meromorphicSectionPresheaf X (L ⊗ N)) where
  app U :=
    { toFun x :=
        { toFun y := meromorphicSectionLocalizedTensor L N x y
          map_add' := by exact meromorphicSectionLocalizedTensor_add_right L N U x
          map_smul' := by exact fun r y ↦ meromorphicSectionLocalizedTensor_smul_right L N U r x y }
      map_add' := fun x y ↦ by
        ext z
        exact meromorphicSectionLocalizedTensor_add_left L N U x y z
      map_smul' := fun r x ↦ by
        ext y
        exact meromorphicSectionLocalizedTensor_smul_left L N U r x y }
  naturality := by exact meromorphicSectionPresheafTensorBilinear_naturality L N

/-- The tensor-product morphism of meromorphic-section presheaves represented by
the localization bilinear map. -/
def meromorphicSectionPresheafTensorHom (L N : X.Modules) :
    PresheafOfModules.Monoidal.tensorObj
      (meromorphicSectionPresheaf X L) (meromorphicSectionPresheaf X N) ⟶
      meromorphicSectionPresheaf X (L ⊗ N) :=
  (meromorphicSectionPresheafTensorBilinear L N).toHom

/-- Locally bijective morphisms of meromorphic-section presheaves. -/
abbrev meromorphicWeakEquivalences :
    MorphismProperty
      (PresheafOfModules
        (ringPresheaf (regularStructureSections X).localizationPresheaf)) :=
  (smallEtaleTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf
      (ringPresheaf (regularStructureSections X).localizationPresheaf))

/-- The tensor product of two locally bijective meromorphic-section morphisms is
locally bijective. -/
theorem meromorphicWeakEquivalences_tensorHom
    {F₁ F₂ G₁ G₂ :
      PresheafOfModules
        (ringPresheaf (regularStructureSections X).localizationPresheaf)}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂)
    (hf : meromorphicWeakEquivalences (X := X) f)
    (hg : meromorphicWeakEquivalences (X := X) g) :
    meromorphicWeakEquivalences (X := X) (f ⊗ₘ g) :=
  sorry

/-- Locally bijective meromorphic-section morphisms form a monoidal morphism
property. -/
instance meromorphicWeakEquivalences.instIsMonoidal :
    (meromorphicWeakEquivalences (X := X)).IsMonoidal :=
  MorphismProperty.IsMonoidal.mk' _ (meromorphicWeakEquivalences_tensorHom (X := X))

/-- The localization functor for meromorphic-section presheaves, as a monoidal
functor into the localized monoidal category. -/
abbrev meromorphicSectionSheafificationMonoidalFunctor :=
  Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.moduleSheafification (smallEtaleTopology X)
      (regularStructureSections X).localizationPresheaf)
    (meromorphicWeakEquivalences (X := X)) (Iso.refl _)

/-- Comparison `𝒦_X(L) ⊗ 𝒦_X(N) ⟶ 𝒦_X(L ⊗ N)` in the localized monoidal
category of meromorphic-section sheaves. -/
def meromorphicSectionSheafTensorHom (L N : X.Modules) :
    meromorphicSectionSheafificationMonoidalFunctor.obj
        (meromorphicSectionPresheaf X L) ⊗
      meromorphicSectionSheafificationMonoidalFunctor.obj
        (meromorphicSectionPresheaf X N) ⟶
      meromorphicSectionSheaf X (L ⊗ N) :=
  (Localization.Monoidal.μ
      (PresheafOfModules.moduleSheafification (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf)
      (meromorphicWeakEquivalences (X := X)) (Iso.refl _)
      (meromorphicSectionPresheaf X L)
      (meromorphicSectionPresheaf X N)).hom ≫
    (PresheafOfModules.moduleSheafification (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf).map
      (meromorphicSectionPresheafTensorHom L N)

/-- Restricted scalars of the structure `𝒦_X`-module, as a module presheaf over
`𝒮⁻¹ 𝒪`. -/
def meromorphicRestrictedUnitPresheaf :
    PresheafOfModules
      (ringPresheaf (regularStructureSections X).localizationPresheaf) :=
  (PresheafOfModules.restrictScalars
      (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf)).obj
    ((SheafOfModules.forget _).obj
      (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X)))

/-- The ring homomorphism `𝒮⁻¹ 𝒪(U) ⟶ 𝒦_X(U)` from the sheafification unit. -/
def meromorphicToSheafifyRingHom (U : (smallEtaleSite X)ᵒᵖ) :
    (ringPresheaf (regularStructureSections X).localizationPresheaf).obj U ⟶
      (ringSheaf (smallEtaleTopology X) (meromorphicFunctionSheaf X)).obj.obj U :=
  (forget₂ CommRingCat RingCat).map
    ((CategoryTheory.toSheafify (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf).app U)

/-- `𝒦_X(U)` is an `𝒮⁻¹ 𝒪(U)`-module via the ring-sheafification unit. -/
noncomputable instance meromorphicRestrictedUnitModule (U : (smallEtaleSite X)ᵒᵖ) :
    Module ((ringPresheaf (regularStructureSections X).localizationPresheaf).obj U)
      (((SheafOfModules.forget _).obj
        (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X))).obj U) :=
  Module.compHom _
    (meromorphicToSheafifyRingHom U).hom

/-- The restricted structure module of `𝒦_X` carries the same `𝒮⁻¹ 𝒪(U)`-action. -/
noncomputable instance meromorphicRestrictedUnitModuleObj (U : (smallEtaleSite X)ᵒᵖ) :
    Module ((ringPresheaf (regularStructureSections X).localizationPresheaf).obj U)
      (meromorphicRestrictedUnitPresheaf.obj U) :=
  inferInstanceAs <|
    Module ((ringPresheaf (regularStructureSections X).localizationPresheaf).obj U)
      (((SheafOfModules.forget _).obj
        (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X))).obj U)

private theorem meromorphicUnitPresheafHomApp_map_add
    (U : (smallEtaleSite X)ᵒᵖ)
    (x y : (𝟙_ (PresheafOfModules
      (ringPresheaf (regularStructureSections X).localizationPresheaf))).obj U) :
    (meromorphicToSheafifyRingHom U).hom (x + y) =
      (meromorphicToSheafifyRingHom U).hom x + (meromorphicToSheafifyRingHom U).hom y := sorry

private theorem meromorphicUnitPresheafHomApp_map_smul
    (U : (smallEtaleSite X)ᵒᵖ)
    (r : (ringPresheaf (regularStructureSections X).localizationPresheaf).obj U)
    (x : (𝟙_ (PresheafOfModules
      (ringPresheaf (regularStructureSections X).localizationPresheaf))).obj U) :
    (meromorphicToSheafifyRingHom U).hom (r • x) =
      r • (show meromorphicRestrictedUnitPresheaf.obj U from
        (meromorphicToSheafifyRingHom U).hom x) := sorry

/-- Objectwise map sending a localized regular function to the corresponding
section of `𝒦_X`. -/
def meromorphicUnitPresheafHomApp (U : (smallEtaleSite X)ᵒᵖ) :
    (𝟙_ (PresheafOfModules
      (ringPresheaf (regularStructureSections X).localizationPresheaf))).obj U ⟶
      meromorphicRestrictedUnitPresheaf.obj U :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦ (meromorphicToSheafifyRingHom U).hom x
      map_add' := by exact meromorphicUnitPresheafHomApp_map_add U
      map_smul' := by exact meromorphicUnitPresheafHomApp_map_smul U }

private theorem meromorphicUnitPresheafHom_naturality
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    (𝟙_ (PresheafOfModules
        (ringPresheaf (regularStructureSections X).localizationPresheaf))).map i ≫
      (ModuleCat.restrictScalars
        ((ringPresheaf (regularStructureSections X).localizationPresheaf).map i).hom).map
          (meromorphicUnitPresheafHomApp V) =
      meromorphicUnitPresheafHomApp U ≫ meromorphicRestrictedUnitPresheaf.map i := sorry

/-- The localization unit of `𝒮⁻¹ 𝒪` maps to the structure `𝒦_X`-module by the
ring-sheafification unit. -/
def meromorphicUnitPresheafHom :
    𝟙_ (PresheafOfModules
        (ringPresheaf (regularStructureSections X).localizationPresheaf)) ⟶
      meromorphicRestrictedUnitPresheaf where
  app := meromorphicUnitPresheafHomApp
  naturality := by exact meromorphicUnitPresheafHom_naturality


/-- Adjunct of `meromorphicUnitPresheafHom`: the localized monoidal unit maps to
the structure `𝒦_X`-module. -/
def meromorphicMonoidalUnitToUnitModule :
    meromorphicSectionSheafificationMonoidalFunctor.obj
        (𝟙_ (PresheafOfModules
          (ringPresheaf (regularStructureSections X).localizationPresheaf))) ⟶
      unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X) :=
  (PresheafOfModules.sheafificationHomEquiv
      (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf)).symm
    meromorphicUnitPresheafHom

/-- Classifying morphism of a meromorphic section, as a map out of the localized
monoidal unit. -/
def meromorphicSectionClassifying {L : X.Modules}
    (s : meromorphicSections X L) :
    meromorphicSectionSheafificationMonoidalFunctor.obj
        (𝟙_ (PresheafOfModules
          (ringPresheaf (regularStructureSections X).localizationPresheaf))) ⟶
      meromorphicSectionSheafificationMonoidalFunctor.obj
        (meromorphicSectionPresheaf X L) :=
  meromorphicMonoidalUnitToUnitModule ≫
    (meromorphicSectionSheaf X L).unitHomEquiv.symm s

/-- The unit section of the free rank-one meromorphic-section presheaf. -/
def meromorphicMonoidalUnitPresheafSection :
    (PresheafOfModules.unit
      (ringPresheaf (regularStructureSections X).localizationPresheaf)).sections :=
  PresheafOfModules.unitHomEquiv
      (PresheafOfModules.unit
        (ringPresheaf (regularStructureSections X).localizationPresheaf))
    (𝟙 _)

/-- Sheafification unit of the free rank-one meromorphic-section presheaf. -/
def meromorphicMonoidalUnitSheafificationUnit :
    PresheafOfModules.unit
        (ringPresheaf (regularStructureSections X).localizationPresheaf) ⟶
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
            (regularStructureSections X).localizationPresheaf)).obj
        ((SheafOfModules.forget _).obj
          (meromorphicSectionSheafificationMonoidalFunctor.obj
            (PresheafOfModules.unit
              (ringPresheaf
                (regularStructureSections X).localizationPresheaf)))) :=
  (PresheafOfModules.sheafificationAdjunction
      (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf)).unit.app
    (PresheafOfModules.unit
      (ringPresheaf (regularStructureSections X).localizationPresheaf))

/-- The unit section of the localized monoidal unit of meromorphic sheaves. -/
def meromorphicMonoidalUnitSection :
    ((PresheafOfModules.restrictScalars
        (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
          (regularStructureSections X).localizationPresheaf)).obj
      ((SheafOfModules.forget _).obj
        (meromorphicSectionSheafificationMonoidalFunctor.obj
          (PresheafOfModules.unit
            (ringPresheaf
              (regularStructureSections X).localizationPresheaf))))).sections :=
  PresheafOfModules.sectionsMap meromorphicMonoidalUnitSheafificationUnit
    meromorphicMonoidalUnitPresheafSection

/-- Tensor of the classifying morphisms of two meromorphic sections. -/
def meromorphicSectionClassifyingTensor {L N : X.Modules}
    (s : meromorphicSections X L) (t : meromorphicSections X N) :
    meromorphicSectionSheafificationMonoidalFunctor.obj
        (𝟙_ (PresheafOfModules
          (ringPresheaf (regularStructureSections X).localizationPresheaf))) ⟶
      meromorphicSectionSheafificationMonoidalFunctor.obj
          (meromorphicSectionPresheaf X L) ⊗
        meromorphicSectionSheafificationMonoidalFunctor.obj
          (meromorphicSectionPresheaf X N) :=
  (λ_
        (meromorphicSectionSheafificationMonoidalFunctor.obj
          (𝟙_ (PresheafOfModules
            (ringPresheaf
              (regularStructureSections X).localizationPresheaf))))).inv ≫
    tensorHom (meromorphicSectionClassifying s) (meromorphicSectionClassifying t)

/-- The tensor product of two meromorphic sections, transported to a meromorphic
section of `L ⊗ N`. -/
def meromorphicSectionTensor {L N : X.Modules}
    (s : meromorphicSections X L) (t : meromorphicSections X N) :
    meromorphicSections X (L ⊗ N) :=
  SheafOfModules.sectionsMap (meromorphicSectionSheafTensorHom L N)
    (SheafOfModules.sectionsMap (meromorphicSectionClassifyingTensor s t)
      meromorphicMonoidalUnitSection)

/-- The tensor of meromorphic sections is the named comparison applied to the
pure `𝒦_X`-tensor of the classifying morphisms. -/
theorem meromorphicSectionTensor_def {L N : X.Modules}
    (s : meromorphicSections X L) (t : meromorphicSections X N) :
    meromorphicSectionTensor s t =
      SheafOfModules.sectionsMap (meromorphicSectionSheafTensorHom L N)
        (SheafOfModules.sectionsMap (meromorphicSectionClassifyingTensor s t)
          meromorphicMonoidalUnitSection) :=
  rfl

/-- Étale-local fraction representatives tensor by the canonical lifted pure tensor,
with denominator the product of their denominators. -/
theorem meromorphicSectionTensor_app_of_representatives {L N : X.Modules}
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (U : (smallEtaleSite X)ᵒᵖ)
    (m : (liftModule L).val.obj U) (n : (liftModule N).val.obj U)
    (a b : (regularStructureSections X).obj U)
    (hs : s.val U = (((PresheafOfModules.sheafificationAdjunction
          (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
            (regularStructureSections X).localizationPresheaf)).unit.app
        (meromorphicSectionPresheaf X L)).app U) (LocalizedModule.mk m a))
    (ht : t.val U = (((PresheafOfModules.sheafificationAdjunction
          (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
            (regularStructureSections X).localizationPresheaf)).unit.app
        (meromorphicSectionPresheaf X N)).app U) (LocalizedModule.mk n b)) :
    (meromorphicSectionTensor s t).val U =
      (((PresheafOfModules.sheafificationAdjunction
          (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
            (regularStructureSections X).localizationPresheaf)).unit.app
        (meromorphicSectionPresheaf X (L ⊗ N))).app U)
        (LocalizedModule.mk (RelativeProj.liftModuleTensorSection L N U m n) (a * b)) := sorry

/-- On a locally Noetherian integral algebraic space, a meromorphic section of an
invertible module is regular exactly when it is nonzero. -/
theorem isRegularMeromorphicSection_iff_ne_zero [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L) :
    IsRegularMeromorphicSection X L s ↔ s ≠ 0 := sorry

/-- The tensor product of nonzero meromorphic sections of invertible modules is
nonzero. -/
theorem meromorphicSectionTensor_ne_zero [IsLocallyNoetherian X] [IsIntegral X]
    {L N : X.Modules}
    [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    meromorphicSectionTensor s t ≠ 0 :=
  sorry

/-- The tensor product of regular meromorphic sections of invertible modules is
regular. -/
theorem isRegularMeromorphicSection_tensor {L N : X.Modules}
    [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X N t) :
    IsRegularMeromorphicSection X (L ⊗ N) (meromorphicSectionTensor s t) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
