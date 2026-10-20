/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.Big
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import Mathlib.CategoryTheory.Whiskering

/-!
# Ringed morphisms between standard scheme sites

The maps on structure sheaves are induced by the projection from each fibre product.  The
small-to-big constructions use the continuous-and-cocontinuous site presentation of the
existing morphisms of topoi and their explicit inverse-image maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u uC vC uD vD

namespace AlgebraicGeometry.Scheme.Site

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A natural map between scheme-valued realizations induces the contravariant map on their
global-sections presheaves. -/
noncomputable def structurePresheafMap
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    (projection : F ⋙ Q ⟶ P) :
    structurePresheaf P ⟶ F.op ⋙ structurePresheaf Q where
  app U := RingCat.ofHom (projection.app U.unop).appTop.hom
  naturality _ _ _ := sorry

/-- The component of `structurePresheafMap` is the usual pullback map on global sections. -/
theorem structurePresheafMap_app
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    (projection : F ⋙ Q ⟶ P) (U : Cᵒᵖ) :
    (structurePresheafMap P Q F projection).app U =
      RingCat.ofHom (projection.app U.unop).appTop.hom := sorry

/-- Bundle the global-sections map as a morphism between the corresponding ring sheaves. -/
noncomputable def structureSheafMap
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    [F.IsContinuous J K] (projection : F ⋙ Q ⟶ P)
    (hP : Presheaf.IsSheaf J (structurePresheaf P))
    (hQ : Presheaf.IsSheaf K (structurePresheaf Q)) :
    (⟨structurePresheaf P, hP⟩ : Sheaf J RingCat.{u}) ⟶
      (F.sheafPushforwardContinuous RingCat.{u} J K).obj
        (⟨structurePresheaf Q, hQ⟩ : Sheaf K RingCat.{u}) :=
  ⟨structurePresheafMap P Q F projection⟩

/-- The sheaf-map component is the map on global sections induced by the realization
projection. -/
theorem structureSheafMap_app
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    [F.IsContinuous J K] (projection : F ⋙ Q ⟶ P)
    (hP : Presheaf.IsSheaf J (structurePresheaf P))
    (hQ : Presheaf.IsSheaf K (structurePresheaf Q)) (U : Cᵒᵖ) :
    (structureSheafMap J K P Q F projection hP hQ).hom.app U =
      RingCat.ofHom (projection.app U.unop).appTop.hom := sorry

/-- A morphism of sites whose scheme realizations are related by a projection induces the
corresponding morphism of ringed sites. -/
noncomputable def ringedHom
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    [IsMorphismOfSites J K F] (projection : F ⋙ Q ⟶ P)
    (hP : Presheaf.IsSheaf J (structurePresheaf P))
    (hQ : Presheaf.IsSheaf K (structurePresheaf Q)) :
    RingedSite.Hom
      (RingedSite.ofRingSheaf K (⟨structurePresheaf Q, hQ⟩ : Sheaf K RingCat.{u}))
      (RingedSite.ofRingSheaf J (⟨structurePresheaf P, hP⟩ : Sheaf J RingCat.{u})) where
  base := F
  isMorphismOfSites := inferInstance
  structureSheafMap := structureSheafMap J K P Q F projection hP hQ

/-- The base functor of the projection-induced ringed-site morphism is the supplied site
functor. -/
theorem ringedHom_base
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    [IsMorphismOfSites J K F] (projection : F ⋙ Q ⟶ P)
    (hP : Presheaf.IsSheaf J (structurePresheaf P))
    (hQ : Presheaf.IsSheaf K (structurePresheaf Q)) :
    (ringedHom J K P Q F projection hP hQ).base = F := sorry

/-- Objectwise, the projection-induced ringed-site structure map is pullback on global
sections. -/
theorem ringedHom_structureSheafMap_app
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    [IsMorphismOfSites J K F] (projection : F ⋙ Q ⟶ P)
    (hP : Presheaf.IsSheaf J (structurePresheaf P))
    (hQ : Presheaf.IsSheaf K (structurePresheaf Q)) (U : Cᵒᵖ) :
    (ringedHom J K P Q F projection hP hQ).structureSheafMap.hom.app U =
      RingCat.ofHom (projection.app U.unop).appTop.hom := sorry

/-- A natural map from one realization to a pulled-back realization induces the opposite
global-sections map. -/
noncomputable def inverseStructurePresheafMap
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    (comparison : P ⟶ F ⋙ Q) :
    F.op ⋙ structurePresheaf Q ⟶ structurePresheaf P where
  app U := RingCat.ofHom (comparison.app U.unop).appTop.hom
  naturality _ _ _ := sorry

/-- The component of `inverseStructurePresheafMap` is the pullback map induced by the
realization comparison. -/
theorem inverseStructurePresheafMap_app
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    (comparison : P ⟶ F ⋙ Q) (U : Cᵒᵖ) :
    (inverseStructurePresheafMap P Q F comparison).app U =
      RingCat.ofHom (comparison.app U.unop).appTop.hom := sorry

/-- Bundle `inverseStructurePresheafMap` as a morphism between the corresponding ring
sheaves. -/
noncomputable def inverseStructureSheafMap
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    [F.IsContinuous J K] (comparison : P ⟶ F ⋙ Q)
    (hP : Presheaf.IsSheaf J (structurePresheaf P))
    (hQ : Presheaf.IsSheaf K (structurePresheaf Q)) :
    (F.sheafPushforwardContinuous RingCat.{u} J K).obj
        (⟨structurePresheaf Q, hQ⟩ : Sheaf K RingCat.{u}) ⟶
      (⟨structurePresheaf P, hP⟩ : Sheaf J RingCat.{u}) :=
  ⟨inverseStructurePresheafMap P Q F comparison⟩

/-- The inverse-image sheaf-map component is induced by the corresponding scheme map. -/
theorem inverseStructureSheafMap_app
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
    [F.IsContinuous J K] (comparison : P ⟶ F ⋙ Q)
    (hP : Presheaf.IsSheaf J (structurePresheaf P))
    (hQ : Presheaf.IsSheaf K (structurePresheaf Q)) (U : Cᵒᵖ) :
    (inverseStructureSheafMap J K P Q F comparison hP hQ).hom.app U =
      RingCat.ofHom (comparison.app U.unop).appTop.hom := sorry

end AlgebraicGeometry.Scheme.Site

namespace AlgebraicGeometry.StandardTopology.Big

variable {S T : Scheme.{u}}

/-- Naturality of the projection from a base-changed scheme to the original scheme. -/
theorem pullbackProjection_naturality (f : T ⟶ S) {U V : Over S} (g : U ⟶ V) :
    ((Over.pullback f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left := sorry

/-- The natural projection from the source scheme of a base-changed object to the source
scheme of the original object. -/
noncomputable def pullbackProjection (f : T ⟶ S) :
    Over.pullback f ⋙ Over.forget T ⟶ Over.forget S where
  app U := pullback.fst U.hom f
  naturality _ _ g := pullbackProjection_naturality f g

/-- The component of `pullbackProjection f` at `U` is the fibre-product projection. -/
theorem pullbackProjection_app (f : T ⟶ S) (U : Over S) :
    (pullbackProjection f).app U = pullback.fst U.hom f := sorry

/-- The direct-image-form structure map for a morphism between standard big sites. -/
noncomputable def structureMap (τ τ' : StandardTopology) (f : T ⟶ S)
    [IsMorphismOfSites (τ'.overTopology S) (τ.overTopology T) (Over.pullback f)] :
    structureSheaf τ' S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (τ'.overTopology S) (τ.overTopology T)).obj (structureSheaf τ T) :=
  Scheme.Site.structureSheafMap (τ'.overTopology S) (τ.overTopology T)
    (Over.forget S) (Over.forget T) (Over.pullback f) (pullbackProjection f)
    (structurePresheaf_isSheaf τ' S) (structurePresheaf_isSheaf τ T)

/-- At `U ⟶ S`, `structureMap τ τ' f` is the usual map
`Γ(U, 𝒪_U) ⟶ Γ(T ×_S U, 𝒪_{T ×_S U})`. -/
theorem structureMap_app (τ τ' : StandardTopology) (f : T ⟶ S)
    [IsMorphismOfSites (τ'.overTopology S) (τ.overTopology T) (Over.pullback f)]
    (U : (Over S)ᵒᵖ) :
    (structureMap τ τ' f).hom.app U =
      RingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom := sorry

/-- A scheme morphism, together with the previously established morphism-of-sites fact,
induces a morphism between its standard big ringed sites. -/
noncomputable def ringedHom (τ τ' : StandardTopology) (f : T ⟶ S)
    [IsMorphismOfSites (τ'.overTopology S) (τ.overTopology T) (Over.pullback f)] :
    RingedSite.Hom (ringedSite τ T) (ringedSite τ' S) where
  base := Over.pullback f
  isMorphismOfSites := inferInstance
  structureSheafMap := structureMap τ τ' f

/-- The base functor of the standard big-site ringed morphism is fibre-product pullback. -/
theorem ringedHom_base (τ τ' : StandardTopology) (f : T ⟶ S)
    [IsMorphismOfSites (τ'.overTopology S) (τ.overTopology T) (Over.pullback f)] :
    (ringedHom τ τ' f).base = Over.pullback f := sorry

/-- The structure-map component of the standard big-site ringed morphism is the usual map on
global sections induced by the fibre-product projection. -/
theorem ringedHom_structureSheafMap_app (τ τ' : StandardTopology) (f : T ⟶ S)
    [IsMorphismOfSites (τ'.overTopology S) (τ.overTopology T) (Over.pullback f)]
    (U : (Over S)ᵒᵖ) :
    (ringedHom τ τ' f).structureSheafMap.hom.app U =
      RingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom := sorry

/-- The standard big-site ringed morphism associated to an identity scheme morphism is the
identity ringed-site morphism. -/
theorem ringedHom_id (τ : StandardTopology) (S : Scheme.{u})
    [IsMorphismOfSites (τ.overTopology S) (τ.overTopology S) (Over.pullback (𝟙 S))] :
    ringedHom τ τ (𝟙 S) = RingedSite.Hom.id (ringedSite τ S) := sorry

/-- Standard big-site ringed morphisms respect composition of scheme morphisms. -/
theorem ringedHom_comp {R S T : Scheme.{u}} (τ₀ τ₁ τ₂ : StandardTopology)
    (f : R ⟶ S) (g : S ⟶ T)
    [IsMorphismOfSites (τ₁.overTopology S) (τ₀.overTopology R) (Over.pullback f)]
    [IsMorphismOfSites (τ₂.overTopology T) (τ₁.overTopology S) (Over.pullback g)]
    [IsMorphismOfSites (τ₂.overTopology T) (τ₀.overTopology R)
      (Over.pullback (f ≫ g))] :
    RingedSite.Hom.comp (ringedHom τ₀ τ₁ f) (ringedHom τ₁ τ₂ g) =
      ringedHom τ₀ τ₂ (f ≫ g) := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.Scheme.Etale.Small

variable {S T : Scheme.{u}}

/-- Naturality of the fibre-product projection on small étale sites. -/
theorem pullbackProjection_naturality (f : T ⟶ S) {U V : S.Etale} (g : U ⟶ V) :
    ((Scheme.smallEtalePullback f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left := sorry

/-- The source-scheme projection associated to small étale base change. -/
noncomputable def pullbackProjection (f : T ⟶ S) :
    Scheme.smallEtalePullback f ⋙ Scheme.smallEtaleToScheme T ⟶
      Scheme.smallEtaleToScheme S where
  app U := pullback.fst U.hom f
  naturality _ _ g := pullbackProjection_naturality f g

/-- The small-étale projection at `U` is the projection from the fibre product. -/
theorem pullbackProjection_app (f : T ⟶ S) (U : S.Etale) :
    (pullbackProjection f).app U = pullback.fst U.hom f := sorry

/-- The direct-image-form map on small-étale structure sheaves. -/
noncomputable def structureMap (f : T ⟶ S) :
    structureSheaf S ⟶
      ((Scheme.smallEtalePullback f).sheafPushforwardContinuous RingCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology).obj (structureSheaf T) :=
  Scheme.Site.structureSheafMap S.smallEtaleTopology T.smallEtaleTopology
    (Scheme.smallEtaleToScheme S) (Scheme.smallEtaleToScheme T)
    (Scheme.smallEtalePullback f) (pullbackProjection f)
    (structurePresheaf_isSheaf S) (structurePresheaf_isSheaf T)

/-- The small-étale structure map is induced by the fibre-product projection on every
object. -/
theorem structureMap_app (f : T ⟶ S) (U : S.Etaleᵒᵖ) :
    (structureMap f).hom.app U =
      RingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom := sorry

/-- A scheme morphism induces a morphism of small étale ringed sites. -/
noncomputable def ringedHom (f : T ⟶ S) :
    RingedSite.Hom (ringedSite T) (ringedSite S) where
  base := Scheme.smallEtalePullback f
  isMorphismOfSites := inferInstance
  structureSheafMap := structureMap f

/-- The base of the small-étale ringed morphism is small-étale base change. -/
theorem ringedHom_base (f : T ⟶ S) :
    (ringedHom f).base = Scheme.smallEtalePullback f := sorry

/-- The structure-map component of the small-étale ringed morphism is pullback along the
fibre-product projection. -/
theorem ringedHom_structureSheafMap_app (f : T ⟶ S) (U : S.Etaleᵒᵖ) :
    (ringedHom f).structureSheafMap.hom.app U =
      RingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom := sorry

/-- The small-étale ringed morphism associated to the identity is the identity. -/
theorem ringedHom_id (S : Scheme.{u}) :
    ringedHom (𝟙 S) = RingedSite.Hom.id (ringedSite S) := sorry

/-- Small-étale ringed morphisms respect composition of scheme morphisms. -/
theorem ringedHom_comp {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    RingedSite.Hom.comp (ringedHom f) (ringedHom g) = ringedHom (f ≫ g) := sorry

end AlgebraicGeometry.Scheme.Etale.Small

namespace AlgebraicGeometry.Scheme.Zariski.Small

variable {S T : Scheme.{u}}

/-- Naturality of the fibre-product projection on small Zariski sites. -/
theorem pullbackProjection_naturality
    (f : T ⟶ S) {U V : S.smallZariskiSite} (g : U ⟶ V) :
    ((Scheme.smallZariskiPullback f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left := sorry

/-- The source-scheme projection associated to small Zariski base change. -/
noncomputable def pullbackProjection (f : T ⟶ S) :
    Scheme.smallZariskiPullback f ⋙ Scheme.smallZariskiToScheme T ⟶
      Scheme.smallZariskiToScheme S where
  app U := pullback.fst U.hom f
  naturality _ _ g := pullbackProjection_naturality f g

/-- The small-Zariski projection at `U` is the projection from the fibre product. -/
theorem pullbackProjection_app (f : T ⟶ S) (U : S.smallZariskiSite) :
    (pullbackProjection f).app U = pullback.fst U.hom f := sorry

/-- The direct-image-form map on small-Zariski structure sheaves. -/
noncomputable def structureMap (f : T ⟶ S) :
    structureSheaf S ⟶
      ((Scheme.smallZariskiPullback f).sheafPushforwardContinuous RingCat.{u}
        S.smallZariskiTopology T.smallZariskiTopology).obj (structureSheaf T) :=
  Scheme.Site.structureSheafMap S.smallZariskiTopology T.smallZariskiTopology
    (Scheme.smallZariskiToScheme S) (Scheme.smallZariskiToScheme T)
    (Scheme.smallZariskiPullback f) (pullbackProjection f)
    (structurePresheaf_isSheaf S) (structurePresheaf_isSheaf T)

/-- The small-Zariski structure map is induced by the fibre-product projection on every
object. -/
theorem structureMap_app (f : T ⟶ S) (U : S.smallZariskiSiteᵒᵖ) :
    (structureMap f).hom.app U =
      RingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom := sorry

/-- A scheme morphism induces a morphism of small Zariski ringed sites. -/
noncomputable def ringedHom (f : T ⟶ S) :
    RingedSite.Hom (ringedSite T) (ringedSite S) where
  base := Scheme.smallZariskiPullback f
  isMorphismOfSites := inferInstance
  structureSheafMap := structureMap f

/-- The base of the small-Zariski ringed morphism is small-Zariski base change. -/
theorem ringedHom_base (f : T ⟶ S) :
    (ringedHom f).base = Scheme.smallZariskiPullback f := sorry

/-- The structure-map component of the small-Zariski ringed morphism is pullback along the
fibre-product projection. -/
theorem ringedHom_structureSheafMap_app (f : T ⟶ S)
    (U : S.smallZariskiSiteᵒᵖ) :
    (ringedHom f).structureSheafMap.hom.app U =
      RingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom := sorry

/-- The small-Zariski ringed morphism associated to the identity is the identity. -/
theorem ringedHom_id (S : Scheme.{u}) :
    ringedHom (𝟙 S) = RingedSite.Hom.id (ringedSite S) := sorry

/-- Small-Zariski ringed morphisms respect composition of scheme morphisms. -/
theorem ringedHom_comp {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    RingedSite.Hom.comp (ringedHom f) (ringedHom g) = ringedHom (f ≫ g) := sorry

end AlgebraicGeometry.Scheme.Zariski.Small
