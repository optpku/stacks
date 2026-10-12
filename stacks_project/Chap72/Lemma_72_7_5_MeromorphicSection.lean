/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Definition_71_10_9_Regular

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

/-- Pointwise pure tensor of commutative module sections. -/
def commPointwiseTensor {A B : commModules X} (U : (smallEtaleSite X)ᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    (PresheafOfModules.Monoidal.tensorObj A.val B.val).obj U :=
  x ⊗ₜ y

/-- Sheaf morphism from the sheafified pointwise tensor of `toComm L` and
`toComm N` to `toComm (L ⊗ N)`. -/
def commTensorComparison (L N : X.Modules) :
    (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf X)).obj
      (PresheafOfModules.Monoidal.tensorObj
        ((toCommModules X).obj L).val ((toCommModules X).obj N).val) ⟶
      (toCommModules X).obj (L ⊗ N) :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf X))
      ((toCommModules X).obj L).val ((toCommModules X).obj N).val).inv ≫
    tensorHom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf X)
        ((toCommModules X).obj L)).hom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf X)
        ((toCommModules X).obj N)).hom ≫
    (commModulesEquivalence X).unit.app
      (tensorObj ((toCommModules X).obj L) ((toCommModules X).obj N))

/-- Universe-lift of a pure tensor of lifted sections, as a section of
`lift (L ⊗ N)`. -/
def liftModuleTensorSection (L N : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (x : (liftModule L).val.obj U) (y : (liftModule N).val.obj U) :
    (liftModule (L ⊗ N)).val.obj U :=
  ULift.up
    ((commTensorComparison L N).val.app U
      ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf X)
          (PresheafOfModules.Monoidal.tensorObj
            ((toCommModules X).obj L).val
            ((toCommModules X).obj N).val)).app U
        (commPointwiseTensor U x.down y.down)))

/-- Objectwise localization bilinear: `(m / s) ⊗ (n / t) ↦ (m ⊗ n) / (s * t)`. -/
def meromorphicSectionLocalizedTensor (L N : X.Modules)
    {U : (smallEtaleSite X)ᵒᵖ}
    (x : LocalizedModule ((regularStructureSections X).obj U)
      ((liftModule L).val.obj U))
    (y : LocalizedModule ((regularStructureSections X).obj U)
      ((liftModule N).val.obj U)) :
    LocalizedModule ((regularStructureSections X).obj U)
      ((liftModule (L ⊗ N)).val.obj U) :=
  LocalizedModule.liftOn x
    (fun p ↦
      LocalizedModule.liftOn y
        (fun q ↦
          LocalizedModule.mk (liftModuleTensorSection L N U p.1 q.1)
            ⟨p.2.1 * q.2.1, Submonoid.mul_mem _ p.2.2 q.2.2⟩)
        sorry)
    sorry

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
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

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

/-- Locally bijective meromorphic-section morphisms are multiplicative. -/
instance meromorphicWeakEquivalences.instIsMultiplicative :
    (meromorphicWeakEquivalences (X := X)).IsMultiplicative :=
  sorry

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

/-- The sheaf of meromorphic sections is the localization functor applied to the
meromorphic-section presheaf. -/
theorem meromorphicSectionSheaf_eq_monoidalObj (L : X.Modules) :
    meromorphicSectionSheaf X L =
      meromorphicSectionSheafificationMonoidalFunctor.obj
        (meromorphicSectionPresheaf X L) :=
  rfl

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

/-- Restricted scalars of the structure `𝒦_X`-module are the restriction of
`unitModule` along the ring-sheafification unit. -/
theorem meromorphicRestrictedUnitPresheaf_eq :
    meromorphicRestrictedUnitPresheaf =
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
            (regularStructureSections X).localizationPresheaf)).obj
        ((SheafOfModules.forget _).obj
          (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X))) :=
  rfl

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

/-- Objectwise map sending a localized regular function to the corresponding
section of `𝒦_X`. -/
def meromorphicUnitPresheafHomApp (U : (smallEtaleSite X)ᵒᵖ) :
    (𝟙_ (PresheafOfModules
      (ringPresheaf (regularStructureSections X).localizationPresheaf))).obj U ⟶
      meromorphicRestrictedUnitPresheaf.obj U :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦ (meromorphicToSheafifyRingHom U).hom x
      map_add' := sorry
      map_smul' := sorry }

/-- The localization unit of `𝒮⁻¹ 𝒪` maps to the structure `𝒦_X`-module by the
ring-sheafification unit. -/
def meromorphicUnitPresheafHom :
    𝟙_ (PresheafOfModules
        (ringPresheaf (regularStructureSections X).localizationPresheaf)) ⟶
      meromorphicRestrictedUnitPresheaf where
  app := meromorphicUnitPresheafHomApp
  naturality := sorry

/-- The global `1` of `𝒦_X`, viewed in the restricted structure module. -/
def meromorphicRestrictedUnitSection :
    ((PresheafOfModules.restrictScalars
        (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
          (regularStructureSections X).localizationPresheaf)).obj
      ((SheafOfModules.forget _).obj
        (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X)))).sections :=
  PresheafOfModules.unitHomEquiv meromorphicRestrictedUnitPresheaf
    meromorphicUnitPresheafHom

/-- The restricted unit section is the image of `1` under the ring-sheafification
unit. -/
theorem meromorphicRestrictedUnitSection_app (U : (smallEtaleSite X)ᵒᵖ) :
    meromorphicRestrictedUnitSection.val U =
      ((PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
          (regularStructureSections X).localizationPresheaf).app U).hom
        (1 : (regularStructureSections X).localizationPresheaf.obj U) :=
  sorry

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

/-- The classifying morphism of a meromorphic section is the adjunct of the
section after the monoidal-unit comparison. -/
theorem meromorphicSectionClassifying_eq {L : X.Modules}
    (s : meromorphicSections X L) :
    meromorphicSectionClassifying s =
      meromorphicMonoidalUnitToUnitModule ≫
        (meromorphicSectionSheaf X L).unitHomEquiv.symm s :=
  rfl

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

/-- The zero meromorphic section, as the image of the zero morphism from `𝒦_X`. -/
instance instZeroMeromorphicSections (L : X.Modules) :
    Zero (meromorphicSections X L) where
  zero := (meromorphicSectionSheaf X L).unitHomEquiv 0

/-- The tensor product of nonzero meromorphic sections of invertible modules is
nonzero. -/
theorem meromorphicSectionTensor_ne_zero {L N : X.Modules}
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
