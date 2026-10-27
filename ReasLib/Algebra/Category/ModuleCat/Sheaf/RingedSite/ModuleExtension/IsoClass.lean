/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Extension.BaerSum
public import ReasLib.CategoryTheory.Abelian.Extension.Classification
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace ModuleExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [hπ : IsFirstOrderThickening π]
variable {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
variable {c : moduleTensor (ideal π) F ⟶ K}

/-- The underlying fixed-endpoint extension of an mixed-scalar extension with prescribed
infinitesimal map, after restriction of scalars along π. -/
def toFixedEndpoint (E : ModuleExtension hπ.isSquareZero F K c) :
    CategoryTheory.Extension ((restrictionAlong π).obj K) ((restrictionAlong π).obj F) where
  E := E.module
  f := E.incl
  g := E.proj
  zero := E.zero
  shortExact := E.shortExact

/-- The underlying fixed-endpoint extension recovers the mixed-scalar inclusion and projection. -/
theorem toFixedEndpoint_spec (E : ModuleExtension hπ.isSquareZero F K c) :
    (toFixedEndpoint E).f = E.incl ∧ (toFixedEndpoint E).g = E.proj := sorry

/-- Restriction of the maps of a short exact sequence preserves their zero composite. -/
theorem restrictExtension_zero (ξ : CategoryTheory.Extension K F) :
    (restrictionAlong π).map ξ.f ≫ (restrictionAlong π).map ξ.g = 0 := sorry

/-- Restriction of scalars preserves the short exact sequence of an extension. -/
theorem restrictExtension_shortExact (ξ : CategoryTheory.Extension K F) :
    (ShortComplex.mk ((restrictionAlong π).map ξ.f) ((restrictionAlong π).map ξ.g)
      (restrictExtension_zero ξ)).ShortExact := sorry

/-- Restriction of scalars along π applied to a fixed-endpoint extension of 𝒪-modules. -/
noncomputable def restrictExtension (ξ : CategoryTheory.Extension K F) :
    CategoryTheory.Extension ((restrictionAlong π).obj K) ((restrictionAlong π).obj F) where
  E := (restrictionAlong π).obj ξ.E
  f := (restrictionAlong π).map ξ.f
  g := (restrictionAlong π).map ξ.g
  zero := restrictExtension_zero ξ
  shortExact := restrictExtension_shortExact ξ

/-- Restriction of scalars along π acts on the endpoint maps of a fixed-endpoint extension. -/
theorem restrictExtension_map (ξ : CategoryTheory.Extension K F) :
    (restrictExtension ξ).f = (restrictionAlong π).map ξ.f ∧
      (restrictExtension ξ).g = (restrictionAlong π).map ξ.g := sorry

/-- The Baer sum with a restricted extension preserves the prescribed infinitesimal action. -/
theorem vaddExtension_compatible (ξ : CategoryTheory.Extension K F)
    (E : ModuleExtension hπ.isSquareZero F K c) :
    CompatibleC hπ.isSquareZero
      (CategoryTheory.Extension.baerSum (toFixedEndpoint E) (restrictExtension ξ)).f
      (CategoryTheory.Extension.baerSum (toFixedEndpoint E) (restrictExtension ξ)).g c := sorry

/-- Translate an extension with prescribed c by the restriction of an 𝒪-module extension,
using the Baer sum in Mod 𝒪'. -/
noncomputable def vaddExtension (ξ : CategoryTheory.Extension K F)
    (E : ModuleExtension hπ.isSquareZero F K c) :
    ModuleExtension hπ.isSquareZero F K c :=
  let S := CategoryTheory.Extension.baerSum (toFixedEndpoint E) (restrictExtension ξ)
  { module := S.E
    incl := S.f
    proj := S.g
    zero := S.zero
    shortExact := S.shortExact
    compatible := vaddExtension_compatible ξ E }

/-- Translating an extension by an 𝒪-module extension does not change the prescribed
infinitesimal map. -/
theorem infMap_vaddExtension (ξ : CategoryTheory.Extension K F)
    (E : ModuleExtension hπ.isSquareZero F K c) :
    infMap hπ.isSquareZero (vaddExtension ξ E).toExtension = c := sorry

/-- Baer-sum translation preserves isomorphism of the underlying fixed-endpoint extensions. -/
theorem vaddExtension_isIsomorphic
    {ξ ξ' : CategoryTheory.Extension K F} (hξ : IsIsomorphic ξ ξ')
    {E E' : ModuleExtension hπ.isSquareZero F K c}
    (hE : IsIsomorphic (toFixedEndpoint E) (toFixedEndpoint E')) :
    IsIsomorphic (toFixedEndpoint (vaddExtension ξ E))
      (toFixedEndpoint (vaddExtension ξ' E')) := sorry

/-- The setoid of extensions with prescribed c, identifying those whose underlying
mixed-scalar sequences are isomorphic as fixed-endpoint extensions. -/
def isomorphicSetoid (c : moduleTensor (ideal π) F ⟶ K) :
    Setoid (ModuleExtension hπ.isSquareZero F K c) :=
  Setoid.comap toFixedEndpoint
    (isIsomorphicSetoid (CategoryTheory.Extension ((restrictionAlong π).obj K)
      ((restrictionAlong π).obj F)))

/-- Isomorphism classes of extensions of ℱ by 𝒦 with prescribed infinitesimal map c. -/
abbrev IsoClass (c : moduleTensor (ideal π) F ⟶ K) :=
  _root_.Quotient (isomorphicSetoid c)

/-- The Baer-sum action of 𝒪-module extension classes on isomorphism classes of extensions
with prescribed c. -/
noncomputable def vadd (ξ : ExtensionClass K F) (E : IsoClass c) : IsoClass c :=
  Quotient.map₂ vaddExtension (fun _ _ hξ _ _ hE ↦ vaddExtension_isIsomorphic hξ hE) ξ E

/-- The Baer-sum action computes on representatives. -/
theorem vadd_mk (ξ : CategoryTheory.Extension K F)
    (E : ModuleExtension hπ.isSquareZero F K c) :
    vadd (Quotient.mk (isIsomorphicSetoid (CategoryTheory.Extension K F)) ξ)
      (Quotient.mk (isomorphicSetoid c) E) =
      Quotient.mk (isomorphicSetoid c) (vaddExtension ξ E) := sorry

/-- The split 𝒪-module extension acts trivially on isomorphism classes. -/
theorem vadd_zero (E : IsoClass c) : vadd (0 : ExtensionClass K F) E = E := sorry

/-- The Baer-sum action is an action of the extension group. -/
theorem vadd_add (ξ η : ExtensionClass K F) (E : IsoClass c) :
    vadd (ξ + η) E = vadd ξ (vadd η E) := sorry

/-- If at least one extension with prescribed c exists, then isomorphism classes form a
principal homogeneous space under the 𝒪-module extension group. -/
theorem existsUnique_vadd (h_exists : Nonempty (ModuleExtension hπ.isSquareZero F K c))
    (E E' : IsoClass c) :
    ∃! ξ : ExtensionClass K F, vadd ξ E = E' := sorry

variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- The Baer-sum action on isomorphism classes depends only on the Ext¹ class of the acting
𝒪-module extension. -/
theorem vadd_congr_toExt {ξ η : ExtensionClass K F}
    (h : ExtensionClass.toExt ξ = ExtensionClass.toExt η) (E : IsoClass c) :
    vadd ξ E = vadd η E := sorry

/-- If a prescribed extension exists, its fixed-endpoint isomorphism classes admit a unique
translation by Ext¹ between any two classes. -/
theorem isoClass_principalHomogeneous
    (h_exists : Nonempty (ModuleExtension hπ.isSquareZero F K c))
    (E E' : IsoClass c) :
    ∃! x : Ext F K 1,
      ∀ ξ : ExtensionClass K F, ExtensionClass.toExt ξ = x ↔ vadd ξ E = E' := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
