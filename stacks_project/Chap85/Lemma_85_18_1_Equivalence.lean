/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import stacks_project.Chap85.Lemma_85_18_1_Cartesian

/-!
# Hypercovering descent equivalence for modules

If `K` is a hypercovering of the terminal presheaf, then
`a^* : Mod(O_C) ⥤ Mod(O)` is fully faithful with essential image the cartesian
`O`-modules on `((C / K)_total, O)`, and `a_*` is a quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

variable {X : RingedSite.{u, v, w}}
variable [h_eq : HasEqualizers X.carrier] [h_pb : HasPullbacks X.carrier]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology (K.simplicial.obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology (K.simplicial.obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory, ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι (overSiteDiagram K.simplicial) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.simplicial.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology (K.simplicial.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient K.simplicial).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl K.simplicial n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap K.simplicial φ).structureMap).IsRightAdjoint]

/-- The adjunction `a^* ⊣ a_*` of module inverse and direct image along the ringed
augmentation of a hypercovering. -/
def moduleAdjunction :
    modulePullback K.simplicial ⊣ modulePushforward K.simplicial :=
  (toAmbient K.simplicial).moduleAdjunction

/-- `moduleAdjunction` is the ringed-topos module adjunction of `toAmbient`. -/
theorem moduleAdjunction_eq :
    moduleAdjunction K = (toAmbient K.simplicial).moduleAdjunction :=
  sorry

/-- Inverse image `a^*` along a hypercovering is full. -/
instance modulePullback_full : (modulePullback K.simplicial).Full :=
  sorry

/-- Inverse image `a^*` along a hypercovering is faithful. -/
instance modulePullback_faithful : (modulePullback K.simplicial).Faithful :=
  sorry

/-- Inverse image `a^*` along a hypercovering is fully faithful. -/
def modulePullback_fullyFaithful : (modulePullback K.simplicial).FullyFaithful :=
  FullyFaithful.ofFullyFaithful _

/-- The unit of `a^* ⊣ a_*` is an isomorphism. -/
theorem unit_app_isIso (F : SheafOfModules.{w} X.structureSheaf) :
    IsIso ((moduleAdjunction K).unit.app F) :=
  sorry

/-- The counit of `a^* ⊣ a_*` is an isomorphism precisely on cartesian `O`-modules. -/
theorem counit_app_isIso_iff_isCartesian
    (G : SheafOfModules.{w} (ringSheaf K.simplicial)) :
    IsIso ((moduleAdjunction K).counit.app G) ↔ IsCartesian K.simplicial G :=
  sorry

/-- The counit of `a^* ⊣ a_*` is an isomorphism on a cartesian `O`-module. -/
theorem counit_app_isIso_of_isCartesian
    (G : SheafOfModules.{w} (ringSheaf K.simplicial))
    (h : IsCartesian K.simplicial G) :
    IsIso ((moduleAdjunction K).counit.app G) :=
  sorry

/-- An `O`-module on `((C / K)_total, O)` lies in the essential image of `a^*` if and only
if it is cartesian. -/
theorem mem_essImage_iff_isCartesian
    (G : SheafOfModules.{w} (ringSheaf K.simplicial)) :
    (modulePullback K.simplicial).essImage G ↔ IsCartesian K.simplicial G :=
  sorry

/-- The functor `a^*` corestricted to cartesian `O`-modules. -/
def cartesianFunctor :
    SheafOfModules.{w} X.structureSheaf ⥤ Cartesian K.simplicial :=
  (cartesianProperty K.simplicial).lift (modulePullback K.simplicial)
    fun F ↦ modulePullback_isCartesian K.simplicial F

/-- On objects, `cartesianFunctor` is module pullback along `a`. -/
theorem cartesianFunctor_obj (F : SheafOfModules.{w} X.structureSheaf) :
    ((cartesianFunctor K).obj F).obj = (modulePullback K.simplicial).obj F :=
  sorry

/-- The functor sending a cartesian `O`-module to `a_*` of its underlying module. -/
def cartesianInverse :
    Cartesian K.simplicial ⥤ SheafOfModules.{w} X.structureSheaf :=
  (cartesianProperty K.simplicial).ι ⋙ modulePushforward K.simplicial

/-- On objects, `cartesianInverse` is module pushforward along `a`. -/
theorem cartesianInverse_obj (G : Cartesian K.simplicial) :
    (cartesianInverse K).obj G = (modulePushforward K.simplicial).obj G.obj :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a^* ⋙ a_*` of hypercovering descent for modules. -/
def cartesianUnitIso :
    𝟭 (SheafOfModules.{w} X.structureSheaf) ≅
      cartesianFunctor K ⋙ cartesianInverse K :=
  NatIso.ofComponents
    (fun F ↦
      @asIso _ _ _ _ ((moduleAdjunction K).unit.app F) (unit_app_isIso K F))
    sorry

/-- The component of `cartesianUnitIso` at `F` is the adjunction unit. -/
theorem cartesianUnitIso_hom_app (F : SheafOfModules.{w} X.structureSheaf) :
    (cartesianUnitIso K).hom.app F = (moduleAdjunction K).unit.app F :=
  sorry

/-- The counit isomorphism `a_* ⋙ a^* ≅ 𝟭` on cartesian `O`-modules. -/
def cartesianCounitIso :
    cartesianInverse K ⋙ cartesianFunctor K ≅ 𝟭 (Cartesian K.simplicial) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianProperty K.simplicial).isoMk
        (@asIso _ _ _ _ ((moduleAdjunction K).counit.app G.obj)
          (counit_app_isIso_of_isCartesian K G.obj G.property)))
    sorry

/-- The component of `cartesianCounitIso` at `G` is the adjunction counit on the underlying
module. -/
theorem cartesianCounitIso_hom_app_hom (G : Cartesian K.simplicial) :
    ((cartesianCounitIso K).hom.app G).hom =
      (moduleAdjunction K).counit.app G.obj :=
  sorry

/-- If `K` is a hypercovering of the terminal presheaf, then `a^*` implements an equivalence
between `O_C`-modules and cartesian `O`-modules, with quasi-inverse `a_*`. -/
def cartesianEquivalence :
    SheafOfModules.{w} X.structureSheaf ≌ Cartesian K.simplicial :=
  CategoryTheory.Equivalence.mk (cartesianFunctor K) (cartesianInverse K)
    (cartesianUnitIso K) (cartesianCounitIso K)

/-- The forward functor of `cartesianEquivalence` is `a^*` corestricted to cartesian
`O`-modules. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence K).functor = cartesianFunctor K :=
  sorry

/-- The inverse functor of `cartesianEquivalence` is `a_*` on cartesian `O`-modules. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence K).inverse = cartesianInverse K :=
  sorry

end RingedSite.Localization.AtSimplicialSR
