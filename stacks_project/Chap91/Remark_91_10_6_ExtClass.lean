/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Extension.BaerSum
public import ReasLib.CategoryTheory.Abelian.Extension.Classification
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import stacks_project.Chap91.Lemma_91_10_3_IsoClass
public import stacks_project.Chap91.Remark_91_10_6_TrivialExtension

/-!
# The 𝒪-module Ext class of an 08MB extension along a trivialization

A trivialization σ : 𝒪 ⟶ 𝒪' lets restriction of scalars along σ send an 08MB mixed-scalar
extension to a genuine 𝒪-module extension of ℱ by 𝒦, hence to a class in Ext ℱ 𝒦 1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

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
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Restriction of scalars along a trivialization turns an 08MB mixed-scalar extension into
an 𝒪-module extension of ℱ by 𝒦, after identifying the endpoints via σ ≫ π = 𝟙 𝒪. -/
noncomputable def restrictScalarsExtension (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c) :
    CategoryTheory.Extension K F where
  E := (restrictionAlong σ).obj E.module
  f := (restrictEndpointIso π σ hσ K).inv ≫ (restrictionAlong σ).map E.incl
  g := (restrictionAlong σ).map E.proj ≫ (restrictEndpointIso π σ hσ F).hom
  zero := sorry
  shortExact := sorry

/-- The left endpoint map of `restrictScalarsExtension` is restriction along σ of the
mixed-scalar inclusion, compared by the endpoint identification. -/
theorem restrictScalarsExtension_f (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c) :
    (restrictScalarsExtension π σ hσ E).f =
      (restrictEndpointIso π σ hσ K).inv ≫ (restrictionAlong σ).map E.incl := sorry

/-- The right endpoint map of `restrictScalarsExtension` is restriction along σ of the
mixed-scalar projection, compared by the endpoint identification. -/
theorem restrictScalarsExtension_g (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c) :
    (restrictScalarsExtension π σ hσ E).g =
      (restrictionAlong σ).map E.proj ≫ (restrictEndpointIso π σ hσ F).hom := sorry

/-- The 𝒪-module extension class of an 08MB extension, obtained by restriction of scalars
along the trivialization. -/
noncomputable def extensionClass (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c) :
    ExtensionClass K F :=
  Quotient.mk (isIsomorphicSetoid (CategoryTheory.Extension K F))
    (restrictScalarsExtension π σ hσ E)

/-- The 𝒪-module extension class computes on the restricted mixed-scalar sequence. -/
theorem extensionClass_mk (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c) :
    extensionClass π σ hσ E =
      Quotient.mk (isIsomorphicSetoid (CategoryTheory.Extension K F))
        (restrictScalarsExtension π σ hσ E) := sorry

/-- Isomorphic 08MB extensions determine the same 𝒪-module extension class along a
trivialization. -/
theorem extensionClass_congr (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    {E E' : ModuleExtension hπ.isSquareZero F K c}
    (h : isomorphicSetoid c E E') :
    extensionClass π σ hσ E = extensionClass π σ hσ E' := sorry

/-- The 𝒪-module extension class of an isomorphism class of 08MB extensions with prescribed
infinitesimal map. -/
noncomputable def isoClassExtensionClass (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K} (E : IsoClass c) :
    ExtensionClass K F :=
  Quotient.lift (extensionClass π σ hσ) (fun _ _ h ↦ extensionClass_congr π σ hσ h) E

/-- The isomorphism-class extension class computes on representatives. -/
theorem isoClassExtensionClass_mk (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c) :
    isoClassExtensionClass π σ hσ (Quotient.mk (isomorphicSetoid c) E) =
      extensionClass π σ hσ E := sorry

/-- The principal-homogeneous-space chart sending an 08MB isomorphism class to its 𝒪-module
extension class along σ, with inverse the Baer translate of the trivial extension. -/
noncomputable def isoClassExtensionClassEquiv (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    IsoClass c ≃ ExtensionClass K F where
  toFun := isoClassExtensionClass π σ hσ
  invFun ξ := vadd ξ (Quotient.mk (isomorphicSetoid c) (trivialExtension π σ hσ c))
  left_inv := sorry
  right_inv := sorry

/-- The PHS chart computes as `isoClassExtensionClass` on the forward map. -/
theorem isoClassExtensionClassEquiv_apply (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) (E : IsoClass c) :
    isoClassExtensionClassEquiv π σ hσ c E = isoClassExtensionClass π σ hσ E := sorry

/-- The inverse of the PHS chart is Baer translation of the trivial 08MB extension. -/
theorem isoClassExtensionClassEquiv_symm_apply (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) (ξ : ExtensionClass K F) :
    (isoClassExtensionClassEquiv π σ hσ c).symm ξ =
      vadd ξ (Quotient.mk (isomorphicSetoid c) (trivialExtension π σ hσ c)) := sorry

variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- The Ext¹ class of an 08MB extension, as an 𝒪-module extension via the trivialization. -/
noncomputable def extClassOn (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c) :
    Ext F K 1 :=
  ExtensionClass.toExt (extensionClass π σ hσ E)

/-- `extClassOn` is `ExtensionClass.toExt` of `extensionClass`. -/
theorem extClassOn_eq (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c) :
    extClassOn π σ hσ E = ExtensionClass.toExt (extensionClass π σ hσ E) := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
