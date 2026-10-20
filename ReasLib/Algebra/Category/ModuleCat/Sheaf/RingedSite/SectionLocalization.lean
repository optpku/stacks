/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.Ring.Sheaf.Localization

/-!
# Localization of module sheaves on a ringed site

For a compatible family of local sections of a commutative ring sheaf, localization of module
sheaves is the canonical same-site pullback along the localization of the coefficient sheaf.
The resulting adjunction gives its reusable universal property, while a natural isomorphism
identifies this model with extension of scalars.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Presheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SectionLocalization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O : Sheaf J CommRingCat.{max u v}}
variable (S : SubmonoidPresheaf O.obj)

/-- The localization map of ring sheaves, in the identity-site form expected by module
pullback. -/
@[stacks 01D1 "localized coefficient sheaf map",
  stacks 0EMD "localized coefficient sheaf map"]
noncomputable abbrev structureMap :
    ringSheaf J O ⟶
      ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj
        (ringSheaf J S.localizationSheaf) :=
  ringedSiteStructureMap S.toLocalizationSheaf

variable [(SheafOfModules.pushforward (structureMap S)).IsRightAdjoint]

/-- Lemma 17.27.2 (01D1) (2) and Lemma 18.44.2 (0EMD): the functor localizing
module sheaves along the chosen sections. -/
@[stacks 01D1 "localization functor for module sheaves",
  stacks 0EMD "localization functor for module sheaves"]
noncomputable def functor :
    ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J S.localizationSheaf :=
  SheafOfModules.pullback (structureMap S)

/-- The localized module sheaf associated to a module sheaf over the original ring sheaf. -/
noncomputable abbrev obj (F : ringedSiteModuleCategory J O) :
    ringedSiteModuleCategory J S.localizationSheaf :=
  (functor S).obj F

/-- Pullback along the localization map is left adjoint to restriction of scalars. -/
@[stacks 0EMD "localization and restriction adjunction"]
noncomputable def adjunction :
    functor S ⊣ restrictionAlong S.toLocalizationSheaf :=
  (SheafOfModules.pullbackPushforwardAdjunction (structureMap S)).ofNatIsoRight
    (SheafOfModules.ChangeOfRings.pushforwardIso
      (ringSheafMap S.toLocalizationSheaf))

/-- Restriction of scalars along the localization morphism is canonically a right adjoint. -/
noncomputable instance restrictionIsRightAdjoint :
    (restrictionAlong S.toLocalizationSheaf).IsRightAdjoint :=
  (adjunction S).isRightAdjoint

/-- The canonical map from a module sheaf to the restriction of its localization. -/
noncomputable def unit (F : ringedSiteModuleCategory J O) :
    F ⟶ (restrictionAlong S.toLocalizationSheaf).obj (obj S F) :=
  (adjunction S).unit.app F

/-- The Hom equivalence characterizing localization of module sheaves. -/
noncomputable def homEquiv (F : ringedSiteModuleCategory J O)
    (G : ringedSiteModuleCategory J S.localizationSheaf) :
    (obj S F ⟶ G) ≃
      (F ⟶ (restrictionAlong S.toLocalizationSheaf).obj G) :=
  (adjunction S).homEquiv F G

/-- The explicit adjoint transpose of a map into the restriction of a localized-ring
module. -/
noncomputable def lift {F : ringedSiteModuleCategory J O}
    {G : ringedSiteModuleCategory J S.localizationSheaf}
    (f : F ⟶ (restrictionAlong S.toLocalizationSheaf).obj G) :
    obj S F ⟶ G :=
  (homEquiv S F G).symm f

/-- The adjoint transpose factors the original map through the localization unit. -/
@[reassoc]
theorem lift_fac {F : ringedSiteModuleCategory J O}
    {G : ringedSiteModuleCategory J S.localizationSheaf}
    (f : F ⟶ (restrictionAlong S.toLocalizationSheaf).obj G) :
    unit S F ≫ (restrictionAlong S.toLocalizationSheaf).map (lift S f) = f := sorry

/-- A map from the localized module with the prescribed restriction is the adjoint
transpose. -/
theorem lift_unique {F : ringedSiteModuleCategory J O}
    {G : ringedSiteModuleCategory J S.localizationSheaf}
    (f : F ⟶ (restrictionAlong S.toLocalizationSheaf).obj G)
    (g : obj S F ⟶ G)
    (hg : unit S F ≫ (restrictionAlong S.toLocalizationSheaf).map g = f) :
    g = lift S f := sorry

/-- Morphisms from a localized module sheaf agree when their restrictions agree after the
localization unit. -/
@[stacks 01D1 "extensionality for localized module sheaves",
  stacks 0EMD "extensionality for localized module sheaves"]
theorem hom_ext {F : ringedSiteModuleCategory J O}
    {G : ringedSiteModuleCategory J S.localizationSheaf}
    {f g : obj S F ⟶ G}
    (h : unit S F ≫ (restrictionAlong S.toLocalizationSheaf).map f =
      unit S F ≫ (restrictionAlong S.toLocalizationSheaf).map g) :
    f = g := sorry

/-- Lemma 18.44.2 (0EMD) (1): maps from a module sheaf to a module over the localized
coefficient sheaf factor uniquely through its localized module. -/
@[stacks 0EMD "universal property of localized module sheaves"]
theorem existsUnique_lift {F : ringedSiteModuleCategory J O}
    {G : ringedSiteModuleCategory J S.localizationSheaf}
    (f : F ⟶ (restrictionAlong S.toLocalizationSheaf).obj G) :
    ∃! g : obj S F ⟶ G,
      unit S F ≫ (restrictionAlong S.toLocalizationSheaf).map g = f := sorry

/-- Lemma 17.27.2 (01D1) (2) and Lemma 18.44.2 (0EMD) (2): localization of
module sheaves is canonically extension of scalars along the localized coefficient sheaf,
the categorical form of `S⁻¹O ⊗_O F`. -/
@[stacks 01D1 "sheafified localized modules as extension of scalars",
  stacks 0EMD "localized modules as extension of scalars"]
noncomputable def extensionIso :
    functor S ≅ SheafOfModules.ChangeOfRings.extendScalars
      (ringSheafMap S.toLocalizationSheaf) :=
  SheafOfModules.ChangeOfRings.extendScalarsIso
    (ringSheafMap S.toLocalizationSheaf) (adjunction S)

/-- The forward pointwise comparison from sheaf localization to extension of scalars. -/
@[stacks 01D1 "localized module comparison to extension of scalars",
  stacks 0EMD "localized module comparison to extension of scalars"]
noncomputable def extensionHom (F : ringedSiteModuleCategory J O) :
    obj S F ⟶
      (SheafOfModules.ChangeOfRings.extendScalars
        (ringSheafMap S.toLocalizationSheaf)).obj F :=
  (extensionIso S).hom.app F

/-- The inverse pointwise comparison from extension of scalars to sheaf localization. -/
@[stacks 01D1 "inverse localized module comparison to extension of scalars",
  stacks 0EMD "inverse localized module comparison to extension of scalars"]
noncomputable def extensionInv (F : ringedSiteModuleCategory J O) :
    (SheafOfModules.ChangeOfRings.extendScalars
        (ringSheafMap S.toLocalizationSheaf)).obj F ⟶ obj S F :=
  (extensionIso S).inv.app F

/-- The forward component of `extensionIso` is the named pointwise comparison. -/
@[simp]
theorem extensionIso_hom_app (F : ringedSiteModuleCategory J O) :
    (extensionIso S).hom.app F = extensionHom S F := sorry

/-- The inverse component of `extensionIso` is the named inverse pointwise comparison. -/
@[simp]
theorem extensionIso_inv_app (F : ringedSiteModuleCategory J O) :
    (extensionIso S).inv.app F = extensionInv S F := sorry

/-- The forward extension comparison followed by its inverse is the identity. -/
@[simp]
theorem extensionHom_comp_extensionInv (F : ringedSiteModuleCategory J O) :
    extensionHom S F ≫ extensionInv S F = 𝟙 (obj S F) := sorry

/-- The inverse extension comparison followed by the forward comparison is the identity. -/
@[simp]
theorem extensionInv_comp_extensionHom (F : ringedSiteModuleCategory J O) :
    extensionInv S F ≫ extensionHom S F =
      𝟙 ((SheafOfModules.ChangeOfRings.extendScalars
        (ringSheafMap S.toLocalizationSheaf)).obj F) := sorry

/-- The forward extension comparison is an isomorphism. -/
instance extensionHom_isIso (F : ringedSiteModuleCategory J O) :
    IsIso (extensionHom S F) := sorry

/-- The inverse extension comparison is an isomorphism. -/
instance extensionInv_isIso (F : ringedSiteModuleCategory J O) :
    IsIso (extensionInv S F) := sorry

/-- The forward extension comparison is natural in the module sheaf. -/
@[reassoc]
theorem extensionHom_naturality {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (functor S).map f ≫ extensionHom S G =
      extensionHom S F ≫
        (SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap S.toLocalizationSheaf)).map f := sorry

/-- The inverse extension comparison is natural in the module sheaf. -/
@[reassoc]
theorem extensionInv_naturality {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (SheafOfModules.ChangeOfRings.extendScalars
        (ringSheafMap S.toLocalizationSheaf)).map f ≫ extensionInv S G =
      extensionInv S F ≫ (functor S).map f := sorry

/-- The forward extension comparison identifies the localization unit with the canonical
extension-restriction unit. -/
@[reassoc, stacks 01D1 "localized module comparison preserves the unit",
  stacks 0EMD "localized module comparison preserves the unit"]
theorem unit_extensionHom (F : ringedSiteModuleCategory J O) :
    unit S F ≫ (restrictionAlong S.toLocalizationSheaf).map (extensionHom S F) =
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap S.toLocalizationSheaf)).unit.app F := sorry

/-- The inverse extension comparison identifies the canonical extension-restriction unit with
the localization unit. -/
@[reassoc, stacks 01D1 "inverse localized module comparison preserves the unit",
  stacks 0EMD "inverse localized module comparison preserves the unit"]
theorem extendUnit_extensionInv (F : ringedSiteModuleCategory J O) :
    (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap S.toLocalizationSheaf)).unit.app F ≫
      (restrictionAlong S.toLocalizationSheaf).map (extensionInv S F) =
        unit S F := sorry

-- These constructions use only the canonical localization map, the selected adjoint supplied by
-- `IsRightAdjoint`, and the existing change-of-rings comparison. Any inherited `sorryAx` is in
-- proof fields of the localization presheaf and its natural transformations.

end SheafOfModules.RingedSite.SectionLocalization
