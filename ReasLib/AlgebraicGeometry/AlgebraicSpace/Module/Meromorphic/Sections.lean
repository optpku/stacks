module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction

/-!
# Meromorphic sections of module sheaves on algebraic spaces

For an algebraic space `X` and an `𝒪_X`-module `ℱ`, the sheaf of meromorphic sections
`𝒦_X(ℱ)` is the sheafification of the presheaf `U ↦ 𝒮_X(U)⁻¹ ℱ(U)`, equivalently
`ℱ ⊗_{𝒪_X} 𝒦_X`. A meromorphic section of `ℱ` is a global section of `𝒦_X(ℱ)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite
open PresheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Modules

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The canonical action of `𝒮_X(U)⁻¹ 𝒪_X(U)` on `𝒮_X(U)⁻¹ ℱ(U)`. -/
noncomputable instance meromorphicSectionModule (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    Module ((regularStructureSections X).localizationPresheaf.obj U)
      (LocalizedModule ((regularStructureSections X).obj U) ((liftModule F).val.obj U)) :=
  LocalizedModule.moduleOfIsLocalization
    (S := (regularStructureSections X).obj U)
    (M := (liftModule F).val.obj U)
    (T := (regularStructureSections X).localizationPresheaf.obj U)

/-- The value `𝒮_X(U)⁻¹ ℱ(U)` of the meromorphic-section presheaf at an étale object. -/
noncomputable abbrev meromorphicSectionObj (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    ModuleCat.{u + 1} ((regularStructureSections X).localizationPresheaf.obj U) :=
  ModuleCat.of ((regularStructureSections X).localizationPresheaf.obj U)
    (LocalizedModule ((regularStructureSections X).obj U) ((liftModule F).val.obj U))

/-- The objectwise value of the meromorphic-section presheaf is the localized module of
sections. -/
theorem meromorphicSectionObj_eq (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    meromorphicSectionObj X F U =
      ModuleCat.of ((regularStructureSections X).localizationPresheaf.obj U)
        (LocalizedModule ((regularStructureSections X).obj U) ((liftModule F).val.obj U)) :=
  rfl

/-- Representative-wise restriction of a localized section `m / s` along an étale morphism. -/
noncomputable def meromorphicSectionRestrictRep (F : X.Modules)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (p : (liftModule F).val.obj U × (regularStructureSections X).obj U) :
    LocalizedModule ((regularStructureSections X).obj V) ((liftModule F).val.obj V) :=
  LocalizedModule.mk ((liftModule F).val.map i p.1)
    ⟨((commStructureSheafLift X).obj.map i).hom p.2,
      (regularStructureSections X).map i p.2.property⟩

/-- Representative-wise restriction of localized sections is independent of the chosen
fraction. -/
theorem meromorphicSectionRestrictRep_wd (F : X.Modules)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (p p' : (liftModule F).val.obj U × (regularStructureSections X).obj U) (hp : p ≈ p') :
    meromorphicSectionRestrictRep X F i p = meromorphicSectionRestrictRep X F i p' :=
  sorry

/-- Target of restriction of localized meromorphic sections. -/
abbrev meromorphicSectionRestrictTarget (F : X.Modules)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :=
  (ModuleCat.restrictScalars
      ((regularStructureSections X).localizationPresheaf.map i).hom).obj
    (meromorphicSectionObj X F V)

/-- Restriction of localized meromorphic sections lands in the restriction of scalars of the
target localized module. -/
theorem meromorphicSectionRestrictTarget_eq (F : X.Modules)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    meromorphicSectionRestrictTarget X F i =
      (ModuleCat.restrictScalars
          ((regularStructureSections X).localizationPresheaf.map i).hom).obj
        (meromorphicSectionObj X F V) :=
  rfl

/-- Restriction of localized meromorphic sections along an étale morphism. -/
noncomputable def meromorphicSectionRestrict (F : X.Modules)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    meromorphicSectionObj X F U ⟶ meromorphicSectionRestrictTarget X F i :=
  ModuleCat.ofHom
    (X := meromorphicSectionObj X F U)
    (Y := meromorphicSectionRestrictTarget X F i)
    { toFun := fun x ↦
        LocalizedModule.liftOn x (meromorphicSectionRestrictRep X F i)
          (meromorphicSectionRestrictRep_wd X F i)
      map_add' := sorry
      map_smul' := sorry }

/-- Applying restriction of localized meromorphic sections recovers the representative-wise
formula on fractions. -/
theorem meromorphicSectionRestrict_mk (F : X.Modules)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (m : (liftModule F).val.obj U) (s : (regularStructureSections X).obj U) :
    meromorphicSectionRestrict X F i (LocalizedModule.mk m s) =
      meromorphicSectionRestrictRep X F i (m, s) :=
  sorry

/-- The presheaf `U ↦ 𝒮_X(U)⁻¹ ℱ(U)` of localized modules of sections. -/
noncomputable def meromorphicSectionPresheaf (F : X.Modules) :
    PresheafOfModules.{u + 1}
      (ringPresheaf (regularStructureSections X).localizationPresheaf) where
  obj := meromorphicSectionObj X F
  map := meromorphicSectionRestrict X F
  map_id := sorry
  map_comp := sorry

/-- The meromorphic-section presheaf evaluates by `meromorphicSectionObj`. -/
theorem meromorphicSectionPresheaf_obj (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    (meromorphicSectionPresheaf X F).obj U = meromorphicSectionObj X F U :=
  rfl

/-- The sheafification unit of the objectwise localization of `𝒪_X` at regular sections is
locally injective. -/
instance localizationPresheaf_sheafificationRingMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (smallEtaleTopology X)
      (sheafificationRingMap (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf) :=
  sorry

/-- The sheafification unit of the objectwise localization of `𝒪_X` at regular sections is
locally surjective. -/
instance localizationPresheaf_sheafificationRingMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (smallEtaleTopology X)
      (sheafificationRingMap (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf) :=
  sorry

/-- For an `𝒪_X`-module sheaf `ℱ`, the sheaf of meromorphic sections `𝒦_X(ℱ)` is the
sheafification of `U ↦ 𝒮_X(U)⁻¹ ℱ(U)`, equivalently `ℱ ⊗_{𝒪_X} 𝒦_X`. -/
noncomputable def meromorphicSectionSheaf (F : X.Modules) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (meromorphicFunctionSheaf X) :=
  (moduleSheafification (smallEtaleTopology X)
      (regularStructureSections X).localizationPresheaf).obj
    (meromorphicSectionPresheaf X F)

/-- `𝒦_X(ℱ)` is the module sheafification of `U ↦ 𝒮_X(U)⁻¹ ℱ(U)` along the
localization of `𝒪_X` at regular sections. -/
theorem meromorphicSectionSheaf_eq (F : X.Modules) :
    meromorphicSectionSheaf X F =
      (moduleSheafification (smallEtaleTopology X)
          (regularStructureSections X).localizationPresheaf).obj
        (meromorphicSectionPresheaf X F) :=
  rfl

/-- A meromorphic section of an `𝒪_X`-module sheaf is a global section of `𝒦_X(ℱ)`. -/
abbrev meromorphicSections (F : X.Modules) : Type (u + 1) :=
  (meromorphicSectionSheaf X F).sections

/-- Meromorphic sections of `ℱ` are the global sections of `𝒦_X(ℱ)`. -/
theorem meromorphicSections_eq_sections (F : X.Modules) :
    meromorphicSections X F = (meromorphicSectionSheaf X F).sections :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
