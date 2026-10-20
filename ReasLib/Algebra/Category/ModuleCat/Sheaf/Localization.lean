/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of module sheaves at an object of a site

This file names the adjoint triple attached to the slice site over an object `U`:
extension from the slice, restriction to the slice, and direct image from the slice.
The constructions are kept at the level of an arbitrary sheaf of rings on a site.
`HasLowerShriek.{z} R` packages the exact reusable hypothesis that extension exists from every
slice in the chosen module universe `z`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w z

namespace SheafOfModules.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The structure-ring morphism underlying restriction to the slice site over `U`. -/
@[stacks 04IX "localization ring morphism"]
abbrev restrictionRingHom (R : Sheaf J RingCat.{w}) (U : C) :
    R.over U ⟶
      ((Over.forget U).sheafPushforwardContinuous RingCat.{w} (J.over U) J).obj R :=
  𝟙 (R.over U)

/-- Restriction of module sheaves to the slice site over `U`. -/
@[stacks 04IX "restriction"]
noncomputable abbrev restriction (R : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over U) :=
  SheafOfModules.pushforward (restrictionRingHom R U)

/-- Extension from every slice of the site exists in the chosen module universe. -/
@[stacks 03DI "extension by zero on all slices"]
class HasLowerShriek.{zM, uC, vC, wR}
    {D : Type uC} [Category.{vC} D] {K : GrothendieckTopology D}
    (R : Sheaf K RingCat.{wR}) : Prop where
  /-- Restriction to each slice has the left adjoint used for extension by zero. -/
  isRightAdjoint (U : D) :
    (restriction R U : SheafOfModules.{zM} R ⥤
      SheafOfModules.{zM} (R.over U)).IsRightAdjoint

attribute [instance] HasLowerShriek.isRightAdjoint

/-- Presheaf-level left adjoints on every slice, together with module sheafification, supply
extension by zero in an arbitrary module universe.  This is a named bridge rather than a global
instance because its pointwise adjoint premise is normally provided explicitly. -/
@[stacks 03DI "extension by zero from presheaf adjoints"]
theorem hasLowerShriekOfPresheafAdjoints
    (R : Sheaf J RingCat.{w})
    (h : ∀ U : C,
      ((PresheafOfModules.pushforward (restrictionRingHom R U).hom) :
        PresheafOfModules.{z} R.obj ⥤
          PresheafOfModules.{z} (R.over U).obj).IsRightAdjoint)
    [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    HasLowerShriek.{z} R := sorry

/-- On a same-universe small site, the standard presheaf pullback construction supplies
extension by zero from every slice. -/
@[stacks 03DI "small-site extension by zero", instance]
theorem hasLowerShriekOfSmallCategory
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (R : Sheaf J RingCat.{w}) : HasLowerShriek.{w} R := sorry

section LowerShriek

variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{z} R ⥤
  SheafOfModules.{z} (R.over U)).IsRightAdjoint]

/-- Extension of module sheaves from the slice site over `U`, defined as the left adjoint of
restriction. -/
@[stacks 04IX "extension by zero"]
noncomputable abbrev lowerShriek :
    SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R :=
  (restriction R U).leftAdjoint

/-- Extension from the slice site over `U` is left adjoint to restriction. -/
@[stacks 03DI "(1)"]
noncomputable def lowerShriekRestrictionAdj :
    lowerShriek R U ⊣ restriction R U :=
  Adjunction.ofIsRightAdjoint (restriction R U)

/-- The Hom equivalence characterizing extension from the slice site as the left adjoint of
restriction. -/
@[stacks 03DI "(1), Hom equivalence"]
noncomputable def lowerShriekHomEquiv
    (G : SheafOfModules.{z} (R.over U)) (F : SheafOfModules.{z} R) :
    ((lowerShriek R U).obj G ⟶ F) ≃ (G ⟶ (restriction R U).obj F) :=
  (lowerShriekRestrictionAdj R U).homEquiv G F

end LowerShriek

section LowerShriekConstruction

variable (R : Sheaf J RingCat.{w}) (U : C)
variable [presheafRestrictionIsRightAdjoint :
  ((PresheafOfModules.pushforward (restrictionRingHom R U).hom) :
  PresheafOfModules.{z} R.obj ⥤
    PresheafOfModules.{z} (R.over U).obj).IsRightAdjoint]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- The canonical presheaf underlying extension from the slice site. It is the presheaf-module
left adjoint of restriction before ambient sheafification. -/
@[stacks 03DI "presheaf lower-shriek model"]
noncomputable abbrev lowerShriekPresheaf :
    SheafOfModules.{z} (R.over U) ⥤ PresheafOfModules.{z} R.obj :=
  SheafOfModules.forget (R.over U) ⋙
    PresheafOfModules.pullback (restrictionRingHom R U).hom

/-- The canonical construction of extension from the slice site is obtained by sheafifying its
presheaf-module left-adjoint model. -/
@[stacks 03DI "(2), associated sheaf construction"]
noncomputable abbrev lowerShriekSheafification :
    SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R :=
  SheafOfModules.forget (R.over U) ⋙
    (PresheafOfModules.pullback (restrictionRingHom R U).hom :
      PresheafOfModules.{z} (R.over U).obj ⥤ PresheafOfModules.{z} R.obj) ⋙
    PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)

/-- The sheafified presheaf construction is left adjoint to restriction. -/
@[stacks 03DI "(1), constructed adjunction"]
noncomputable def lowerShriekSheafificationAdj :
    lowerShriekSheafification R U ⊣
      (restriction R U : SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over U)) :=
  @SheafOfModules.PullbackConstruction.adjunction _ _ _ _ _ _ _ _ _ _
    (restrictionRingHom R U) presheafRestrictionIsRightAdjoint _ _

/-- Under the standard presheaf-adjoint and sheafification hypotheses, restriction to the slice
site has a left adjoint. This named instance lets downstream code infer extension from the slice
without rebuilding local adjunction instances. -/
@[stacks 03DI "extension-by-zero existence"]
noncomputable instance restrictionIsRightAdjoint :
    (restriction R U : SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (R.over U)).IsRightAdjoint :=
  (lowerShriekSheafificationAdj R U).isRightAdjoint

/-- Abstract extension from the slice site agrees with the canonical presheaf-left-adjoint
construction followed by sheafification. -/
@[stacks 03DI "(2), comparison"]
noncomputable def lowerShriekSheafificationIso :
    (lowerShriek R U : SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R) ≅
      lowerShriekSheafification R U :=
  Adjunction.leftAdjointUniq (lowerShriekRestrictionAdj R U)
    (lowerShriekSheafificationAdj R U)

end LowerShriekConstruction

section StructureModule

variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]

/-- The module sheaf obtained by extending the unit module on the slice site over `U`. -/
@[stacks 03DI "extension of the unit module"]
noncomputable abbrev structureModule :
    SheafOfModules.{w} R :=
  (lowerShriek R U).obj (SheafOfModules.unit (R.over U))

/-- Morphisms from the module sheaf represented by `U` are sections over `U`, equivalently
elements of the target module at `U`. -/
@[stacks 03DI "represented sections", stacks 0G1V]
noncomputable def structureModuleHomEquiv
    (M : SheafOfModules.{w} R) :
    (structureModule R U ⟶ M) ≃ M.val.obj (op U) :=
  ((lowerShriekRestrictionAdj R U).homEquiv _ _).trans
    (((restriction R U).obj M).unitHomEquiv.trans (SheafOfModules.sectionsOverEquiv M U))

/-- The Type-valued evaluation functor at `U` used by the structure-module corepresentation. -/
@[stacks 0G1V "sections functor"]
abbrev sectionsAt : SheafOfModules.{w} R ⥤ Type w :=
  SheafOfModules.evaluation R (op U) ⋙
    CategoryTheory.forget (ModuleCat.{w} (R.obj.obj (op U)))

/-- The represented-sections equivalence is natural in the target module. -/
@[stacks 0G1V "represented sections naturality"]
theorem structureModuleHomEquiv_comp
    {M N : SheafOfModules.{w} R}
    (f : structureModule R U ⟶ M) (g : M ⟶ N) :
    structureModuleHomEquiv R U N (f ≫ g) =
      (sectionsAt R U).map g (structureModuleHomEquiv R U M f) := sorry

/-- The localized structure module corepresents evaluation at the corresponding site object. -/
@[stacks 0G1V "structure-module corepresentability"]
noncomputable def structureModuleCorepresentable :
    (sectionsAt R U).CorepresentableBy (structureModule R U) where
  homEquiv := fun {M} ↦ structureModuleHomEquiv R U M
  homEquiv_comp := fun g f ↦ structureModuleHomEquiv_comp R U f g

end StructureModule

section StructureModuleFunctor

variable (R : Sheaf J RingCat.{w})

/-- A map of site objects induces the covariant map between their localized structure modules,
characterized by restriction of the universal section. -/
@[stacks 03DI "functoriality"]
noncomputable def structureModuleMap {U V : C}
    [(restriction R U : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over U)).IsRightAdjoint]
    [(restriction R V : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over V)).IsRightAdjoint]
    (f : U ⟶ V) : structureModule R U ⟶ structureModule R V :=
  (structureModuleHomEquiv R U (structureModule R V)).symm
    (((structureModule R V).val.map f.op)
      (structureModuleHomEquiv R V (structureModule R V) (𝟙 _)))

/-- Under the represented-sections equivalence, precomposition by `structureModuleMap R f` is
restriction of sections along `f`. -/
theorem structureModuleMap_homEquiv {U V : C}
    [(restriction R U : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over U)).IsRightAdjoint]
    [(restriction R V : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over V)).IsRightAdjoint]
    (f : U ⟶ V) (M : SheafOfModules.{w} R) (α : structureModule R V ⟶ M) :
    structureModuleHomEquiv R U M (structureModuleMap R f ≫ α) =
      M.val.map f.op (structureModuleHomEquiv R V M α) := sorry

/-- The localized-structure-module map associated to an identity is an identity. -/
@[simp]
theorem structureModuleMap_id (U : C)
    [(restriction R U : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over U)).IsRightAdjoint] :
    structureModuleMap R (𝟙 U) = 𝟙 (structureModule R U) := sorry

/-- Localized-structure-module maps respect composition. -/
@[simp, reassoc]
theorem structureModuleMap_comp {U V W : C}
    [(restriction R U : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over U)).IsRightAdjoint]
    [(restriction R V : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over V)).IsRightAdjoint]
    [(restriction R W : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over W)).IsRightAdjoint]
    (f : U ⟶ V) (g : V ⟶ W) :
    structureModuleMap R (f ≫ g) = structureModuleMap R f ≫ structureModuleMap R g := sorry

/-- Localized structure modules form a covariant functor of the site object. -/
@[stacks 03DI "structure-module functor"]
noncomputable def structureModuleFunctor
    [∀ U : C, (restriction R U : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over U)).IsRightAdjoint] :
    C ⥤ SheafOfModules.{w} R where
  obj U := structureModule R U
  map f := structureModuleMap R f
  map_id U := structureModuleMap_id R U
  map_comp f g := structureModuleMap_comp R f g

end StructureModuleFunctor

section DirectImage

variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{z} R ⥤
  SheafOfModules.{z} (R.over U)).IsLeftAdjoint]

/-- Direct image of module sheaves from the slice site over `U`. -/
@[stacks 04IX "direct image"]
noncomputable abbrev directImage :
    SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R :=
  (restriction R U).rightAdjoint

/-- Restriction to the slice site over `U` is left adjoint to direct image. -/
@[stacks 04IX "restriction-direct image adjunction"]
noncomputable def restrictionDirectImageAdj :
    restriction R U ⊣ directImage R U :=
  Adjunction.ofIsLeftAdjoint (restriction R U)

/-- The Hom equivalence characterizing direct image from the slice site as the right adjoint of
restriction. -/
@[stacks 04IX "restriction-direct image Hom equivalence"]
noncomputable def restrictionDirectImageHomEquiv (F : SheafOfModules.{z} R)
    (G : SheafOfModules.{z} (R.over U)) :
    ((restriction R U).obj F ⟶ G) ≃ (F ⟶ (directImage R U).obj G) :=
  (restrictionDirectImageAdj R U).homEquiv F G

end DirectImage

section DirectImageOfProducts

variable [HasBinaryProducts C]

/-- Binary products provide the standard explicit right adjoint to restriction via
`Over.star U`.  The instance is separate from the abstract direct-image owner, so downstream
constructions with a different right-adjoint model need not assume products. -/
@[stacks 04IX "direct image via products"]
noncomputable instance restrictionIsLeftAdjoint
    (R : Sheaf J RingCat.{w}) (U : C) :
    (restriction R U : SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (R.over U)).IsLeftAdjoint :=
  (SheafOfModules.overPushforwardOverAdj (R := R) U).isLeftAdjoint

end DirectImageOfProducts

section SmallSiteLowerShriek

variable {D : Type w} [SmallCategory D] {K : GrothendieckTopology D}
variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (R : Sheaf K RingCat.{w})

end SmallSiteLowerShriek

section RestrictionInstances

variable (R : Sheaf J RingCat.{w}) (U : C)

/-- Restriction of module sheaves to the slice site over `U` preserves finite limits. -/
@[stacks 04IX "exactness of restriction, finite limits"]
instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits
      (restriction R U : SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over U)) := sorry

/-- Restriction of module sheaves to the slice site over `U` preserves finite colimits. -/
@[stacks 04IX "exactness of restriction, finite colimits"]
instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits
      (restriction R U : SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over U)) := sorry

end RestrictionInstances

end SheafOfModules.Localization
