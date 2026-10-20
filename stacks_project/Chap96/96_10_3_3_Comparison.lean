/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap96.Lemma_96_8_1_Comparison
public import stacks_project.Chap96.«96_10_3_1_Comparison»
public import stacks_project.Chap96.«96_10_3_3_Restriction»
public import ReasLib.CategoryTheory.Functor.KanExtension.SmallSections
public import ReasLib.CategoryTheory.Sites.Pushforward.SmallSectionsRing
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Adjunction
public import stacks_project.Chap96.«96_10_3_3_RepresentedSections»

/-!
# Algebraic-space comparison morphisms of étale modules

A 2-commutative triangle of 1-morphisms of categories fibred in groupoids, with
`𝒰` and `𝒱` represented by algebraic spaces `U` and `V`, induces a comparison
morphism `c_φ : a_small^*(g^* F |_{V_étale}) ⟶ f^* F |_{U_étale}` of
`𝒪_{U_étale}`-modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open RingedSite.Hom
open CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- A composite of total functors is continuous for associated étale topologies. -/
instance toFunctor_comp_isContinuous_etale {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    (toFunctor h ⋙ toFunctor k).IsContinuous X.etaleTopology Z.etaleTopology :=
  Functor.isContinuous_comp (toFunctor h) (toFunctor k)
    X.etaleTopology Y.etaleTopology Z.etaleTopology

/-- Associated étale topologies admit type-valued sheafification in universe `u`. -/
instance etaleTopology_hasSheafify_type (X : GroupoidsOver S) :
    HasSheafify X.etaleTopology (Type u) :=
  sorry

/-- Associated étale topologies admit weak type-valued sheafification in universe `u`. -/
instance etaleTopology_hasWeakSheafify_type (X : GroupoidsOver S) :
    HasWeakSheafify X.etaleTopology (Type u) :=
  sorry

/-- Pointwise right Kan extensions exist for type-valued presheaves along a cartesian
total functor. -/
instance toCartesian_op_hasPointwiseRightKanExtension_type {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (P : X.totalᵒᵖ ⥤ Type u)
    [hP : ∀ Z : Y.totalᵒᵖ,
      Small.{u} (StructuredArrow.proj Z (toCartesianBasedFunctor h).toFunctor.op ⋙ P).sections] :
    (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P :=
  Functor.hasPointwiseRightKanExtension_of_small_sections
    (toCartesianBasedFunctor h).toFunctor.op P

/-- Pointwise right Kan extensions exist for ring-valued presheaves along a cartesian
total functor. -/
instance toCartesian_op_hasPointwiseRightKanExtension_ring {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (P : X.totalᵒᵖ ⥤ RingCat.{u})
    [hP : ∀ Z : Y.totalᵒᵖ,
      Small.{u} ((StructuredArrow.proj Z (toCartesianBasedFunctor h).toFunctor.op ⋙ P)
        ⋙ forget RingCat.{u}).sections] :
    (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P :=
  Functor.hasPointwiseRightKanExtension_ring_of_small_sections
    (toCartesianBasedFunctor h).toFunctor.op P

/-- The cartesian total functor is continuous for associated étale topologies. -/
instance toCartesianBasedFunctor_isContinuous_etale {X Y : GroupoidsOver S}
    (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor.IsContinuous
      X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

/-- The cartesian total functor is cocontinuous for associated étale topologies. -/
instance toCartesianBasedFunctor_isCocontinuous_etale {X Y : GroupoidsOver S}
    (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor.IsCocontinuous
      X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

/-- Continuity of the base of `etaleSiteHom` on the étale ringed sites. -/
instance etaleSiteHom_base_isContinuous {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (etaleSiteHom h).base.IsContinuous
      (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology :=
  (etaleSiteHom h).isMorphismOfSites.toIsContinuous

/-- Continuity of a composite of `etaleSiteHom` bases. -/
instance etaleSiteHom_baseComp_isContinuous {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    ((etaleSiteHom h).base ⋙ (etaleSiteHom k).base).IsContinuous
      (etaleRingedSite X).siteTopology (etaleRingedSite Z).siteTopology :=
  Functor.isContinuous_comp (etaleSiteHom h).base (etaleSiteHom k).base
    (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology
    (etaleRingedSite Z).siteTopology

/-- The composite structure-sheaf map along `toFunctor h ⋙ toFunctor k`. -/
def etaleSiteHom_structureSheafMap_compData {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    (etaleRingedSite X).structureSheaf ⟶
      ((toFunctor h ⋙ toFunctor k).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Z.etaleTopology).obj (etaleRingedSite Z).structureSheaf :=
  (etaleSiteHom h).structureSheafMap ≫
    ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).map (etaleSiteHom k).structureSheafMap

/-- Module inverse image along a composite, before transporting the total functor. -/
def etaleModuleInverseImage_comp₀ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleModuleInverseImage k ⋙ etaleModuleInverseImage h ≅
      SheafOfModules.pushforward (etaleSiteHom_structureSheafMap_compData h k) :=
  SheafOfModules.pushforwardComp (etaleSiteHom h).structureSheafMap
    (etaleSiteHom k).structureSheafMap

/-- Transport of composite inverse image along the real total-functor composition
isomorphism. -/
def etaleModuleInverseImage_comp₁ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    SheafOfModules.pushforward (etaleSiteHom_structureSheafMap_compData h k) ≅
      SheafOfModules.pushforward
        (etaleSiteHom_structureSheafMap_compData h k ≫
          (sheafPushforwardContinuousNatTrans
              (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
              RingCat.{u} X.etaleTopology Z.etaleTopology).app
            (etaleRingedSite Z).structureSheaf) :=
  SheafOfModules.pushforwardNatIso (etaleSiteHom_structureSheafMap_compData h k)
    (ObjectProperty.FullSubbicategory.toFunctor.compIso h k)

/-- The transported composite structure-sheaf map agrees with the structure-sheaf
map of the composite 1-morphism. -/
theorem etaleSiteHom_structureSheafMap_comp {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleSiteHom_structureSheafMap_compData h k ≫
        (sheafPushforwardContinuousNatTrans
            (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
            RingCat.{u} X.etaleTopology Z.etaleTopology).app
          (etaleRingedSite Z).structureSheaf =
      (etaleSiteHom (h ≫ k)).structureSheafMap :=
  sorry

/-- Align the transported composite inverse image with inverse image along the
composite 1-morphism. -/
def etaleModuleInverseImage_comp₂ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    SheafOfModules.pushforward
        (etaleSiteHom_structureSheafMap_compData h k ≫
          (sheafPushforwardContinuousNatTrans
              (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
              RingCat.{u} X.etaleTopology Z.etaleTopology).app
            (etaleRingedSite Z).structureSheaf) ≅
      etaleModuleInverseImage (h ≫ k) :=
  SheafOfModules.pushforwardCongr (etaleSiteHom_structureSheafMap_comp h k)

/-- Inverse image of étale modules along a composite 1-morphism is the composite
of the inverse images, via `pushforwardComp` and the real total-functor
composition isomorphism. -/
def etaleModuleInverseImage_comp {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleModuleInverseImage k ⋙ etaleModuleInverseImage h ≅
      etaleModuleInverseImage (h ≫ k) :=
  etaleModuleInverseImage_comp₀ h k ≪≫
    etaleModuleInverseImage_comp₁ h k ≪≫ etaleModuleInverseImage_comp₂ h k

/-- The structure-sheaf map of `h₂` transported along `toFunctorIso e` agrees with
the structure-sheaf map of `h₁`. -/
theorem etaleSiteHom_structureSheafMap_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y}
    (e : h₁ ≅ h₂) :
    (etaleSiteHom h₂).structureSheafMap ≫
        (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
            X.etaleTopology Y.etaleTopology).app
          (etaleRingedSite Y).structureSheaf =
      (etaleSiteHom h₁).structureSheafMap :=
  sorry

/-- Transport of inverse image along the real total-functor isomorphism. -/
def etaleModuleInverseImage_iso₀ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    etaleModuleInverseImage h₂ ≅
      SheafOfModules.pushforward
        ((etaleSiteHom h₂).structureSheafMap ≫
          (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
              X.etaleTopology Y.etaleTopology).app
            (etaleRingedSite Y).structureSheaf) :=
  SheafOfModules.pushforwardNatIso (etaleSiteHom h₂).structureSheafMap (toFunctorIso e)

/-- Align the transported inverse image with inverse image along `h₁`. -/
def etaleModuleInverseImage_iso₁ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    SheafOfModules.pushforward
        ((etaleSiteHom h₂).structureSheafMap ≫
          (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
              X.etaleTopology Y.etaleTopology).app
            (etaleRingedSite Y).structureSheaf) ≅
      etaleModuleInverseImage h₁ :=
  SheafOfModules.pushforwardCongr (etaleSiteHom_structureSheafMap_iso e)

/-- A 2-isomorphism of 1-morphisms induces an isomorphism of étale module
inverse images, via the underlying total-functor isomorphism `toFunctorIso`. -/
def etaleModuleInverseImage_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    etaleModuleInverseImage h₁ ≅ etaleModuleInverseImage h₂ :=
  (etaleModuleInverseImage_iso₀ e ≪≫ etaleModuleInverseImage_iso₁ e).symm

/-- 2-cell transport `a^* g^* ≅ f^*` on étale modules. -/
def etaleModuleInverseImage_twoCell {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f) :
    etaleModuleInverseImage g ⋙ etaleModuleInverseImage a ≅
      etaleModuleInverseImage f :=
  etaleModuleInverseImage_comp a g ≪≫ etaleModuleInverseImage_iso φ

/-- Evaluation of a restricted CFG module at `W` recovers sections at `u_V(W)`. -/
def restrictDirectImageComparison_leftEval {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S}
    [HasSmallCFGTypeSections (S := S) a]
    (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H))).obj.obj (op W) ≅
      ((ToInternal.underlying (etaleRingedSite Vcfg).structureSheaf).obj
        ((etaleModuleDirectImage a).obj H)).obj.obj
          (op ((smallEtaleFunctor V Vcfg eV).obj W)) :=
  Iso.refl _

/-- The comma category computing CFG pushforward at `u_V(W)`. -/
abbrev restrictDirectImageComparison_bigIndex {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S} (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :=
  StructuredArrow (op ((smallEtaleFunctor V Vcfg eV).obj W))
    (toCartesianBasedFunctor a).toFunctor.op

/-- The comma category computing small étale pushforward at `W ×_V U`. -/
abbrev restrictDirectImageComparison_smallIndex {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :=
  AlgebraicSpace.compareSmallIndex (moduleComparisonSpaceMorphism a eU eV) W

/-- Kan diagram for CFG pushforward of the underlying sheaf at `u_V(W)`. -/
abbrev restrictDirectImageComparison_bigDiag {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S} (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_bigIndex a eV W ⥤ Type u :=
  StructuredArrow.proj (op ((smallEtaleFunctor V Vcfg eV).obj W))
      (toCartesianBasedFunctor a).toFunctor.op ⋙
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf).obj H).obj

/-- Kan diagram for small étale pushforward of the restricted underlying sheaf. -/
abbrev restrictDirectImageComparison_smallDiag {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_smallIndex a eU eV W ⥤ Type u :=
  StructuredArrow.proj
      (op ((AlgebraicSpace.etaleBaseChange
          (moduleComparisonSpaceMorphism a eU eV)).obj W))
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces U).op ⋙
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj
      ((restrictModules eU).obj H)).obj

/-- The morphism `a(u_U(T')) ⟶ u_V(W)` in `Vcfg`, obtained by transporting the
identity-presentation comparison morphism of `96.10.3.1` along `eV`. -/
def restrictDirectImageComparison_indexHom {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V)
    (k : restrictDirectImageComparison_smallIndex a eU eV W) :
    (toCartesianBasedFunctor a).toFunctor.obj
        ((smallEtaleFunctor U Ucfg eU).obj k.right.unop) ⟶
      (smallEtaleFunctor V Vcfg eV).obj W :=
  let x := (smallEtaleToGroupoids U).obj k.right.unop
  let z := (smallEtaleToGroupoids V).obj W
  let ψ := RepresentedDirectImage.presentedMorphism a eU eV
  let β : (toFunctor ψ).obj x ⟶ z :=
    (CategoryOfElements.homMk (unop z) (unop ((toFunctor ψ).obj x))
      (((eqToIso (comm ψ)).app x).hom ≫
        AlgebraicSpace.compareOverHom (moduleComparisonSpaceMorphism a eU eV) k).op
      sorry).op
  (eqToIso (cartesian_toFunctor_eq a)).hom.app ((toFunctor eU.hom).obj x) ≫
    (RepresentedDirectImage.targetCounitIso eV).inv.app _ ≫
    (toFunctor eV.hom).map
      ((toFunctor eV.inv).map
          ((ObjectProperty.FullSubbicategory.toFunctor.compIso eU.hom a).hom.app x) ≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso (eU.hom ≫ a) eV.inv).hom.app x ≫
        β)

/-- Opposite form of `restrictDirectImageComparison_indexHom`, as a structured arrow. -/
def restrictDirectImageComparison_indexArrow {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V)
    (k : restrictDirectImageComparison_smallIndex a eU eV W) :
    op ((smallEtaleFunctor V Vcfg eV).obj W) ⟶
      (toCartesianBasedFunctor a).toFunctor.op.obj
        (op ((smallEtaleFunctor U Ucfg eU).obj k.right.unop)) :=
  (restrictDirectImageComparison_indexHom a eU eV W k).op

/-- Functor from the small-étale Kan comma category to the CFG Kan comma category. -/
def restrictDirectImageComparison_indexMap {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_smallIndex a eU eV W ⥤
      restrictDirectImageComparison_bigIndex a eV W where
  obj k := StructuredArrow.mk (restrictDirectImageComparison_indexArrow a eU eV W k)
  map {k k'} α :=
    StructuredArrow.homMk ((smallEtaleFunctor U Ucfg eU).map α.right.unop).op sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The Kan diagrams agree after restriction along `restrictDirectImageComparison_indexMap`. -/
def restrictDirectImageComparison_diagIso {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_indexMap a eU eV W ⋙
        restrictDirectImageComparison_bigDiag a eV H W ≅
      restrictDirectImageComparison_smallDiag a eU eV H W :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Type-valued limits exist for the small-étale Kan diagram at `W ×_V U`. -/
instance restrictDirectImageComparison_smallDiag_hasLimit {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    HasLimit (restrictDirectImageComparison_smallDiag a eU eV H W) :=
  AlgebraicSpace.EtaleTopos.allChartHasLimit U
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
    ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W)

/-- Type-valued limits exist after restriction along the index functor. -/
instance restrictDirectImageComparison_indexBigDiag_hasLimit {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    HasLimit
      (restrictDirectImageComparison_indexMap a eU eV W ⋙
        restrictDirectImageComparison_bigDiag a eV H W) :=
  hasLimit_of_iso (restrictDirectImageComparison_diagIso a eU eV H W).symm

section RepresentedBigLimit

variable {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
variable (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
variable (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
variable (W : AlgebraicSpace.smallEtaleSite V)

include eU in
/-- The actual fibre-atlas/kernel-pair descent cone for the original CFG comma
diagram. Its construction uses each comma arrow into the specified target chart. -/
def restrictDirectImageComparison_bigCone :
    Cone (restrictDirectImageComparison_bigDiag a eV H W) :=
  RepresentedDirectImage.cone a eU eV
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf).obj H)
    ((smallEtaleFunctor V Vcfg eV).obj W)

include eU in
/-- The universal lift evaluates the supplied cone at the actual fibre atlas
comma object and records its kernel-pair compatibility. -/
def restrictDirectImageComparison_bigConeIsLimit :
    IsLimit (restrictDirectImageComparison_bigCone a eU eV H W) :=
  RepresentedDirectImage.coneIsLimit a eU eV
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf).obj H)
    ((smallEtaleFunctor V Vcfg eV).obj W)

include eU in
/-- The represented limit cone consists of the actual atlas descent carrier
and its concrete universal lift. -/
def restrictDirectImageComparison_bigLimitCone :
    LimitCone (restrictDirectImageComparison_bigDiag a eV H W) :=
  ⟨restrictDirectImageComparison_bigCone a eU eV H W,
    restrictDirectImageComparison_bigConeIsLimit a eU eV H W⟩

include eU in
/-- The given presentations provide a limit of the original comma diagram. -/
theorem restrictDirectImageComparison_bigDiag_hasLimit :
    HasLimit (restrictDirectImageComparison_bigDiag a eV H W) :=
  HasLimit.mk (restrictDirectImageComparison_bigLimitCone a eU eV H W)

end RepresentedBigLimit

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category. -/
def restrictDirectImageComparison_limitHom {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    (restrictDirectImageComparison_bigLimitCone a eU eV H W).cone.pt ⟶
      limit (restrictDirectImageComparison_smallDiag a eU eV H W) :=
  limit.lift (restrictDirectImageComparison_smallDiag a eU eV H W)
    ((Cone.postcompose (restrictDirectImageComparison_diagIso a eU eV H W).hom).obj
      ((restrictDirectImageComparison_bigLimitCone a eU eV H W).cone.whisker
        (restrictDirectImageComparison_indexMap a eU eV W)))

/-- Evaluation of `a_small,*` of a restricted module at `W` compared with the
CFG pushforward at `u_V(W)`, via the two Kan-extension limits. -/
def restrictDirectImageComparison_rightEval {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf ⋙
          (etaleRingedToposHom a).toTopos.pushforward).obj H).obj.obj
        (op ((smallEtaleFunctor V Vcfg eV).obj W)) ⟶
      ((ToInternal.underlying (AlgebraicSpace.structureSheaf U) ⋙
            (AlgebraicSpace.ringedToposHom
                (moduleComparisonSpaceMorphism a eU eV)).toTopos.pushforward).obj
          ((restrictModules eU).obj H)).obj.obj (op W) :=
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  letI := restrictDirectImageComparison_bigDiag_hasLimit a eU eV H W
  (restrictDirectImageComparison_bigConeIsLimit a eU eV H W).lift
      (limit.cone (restrictDirectImageComparison_bigDiag a eV H W)) ≫
    restrictDirectImageComparison_limitHom a eU eV H W ≫
      (limit.isoLimitCone
        ⟨AlgebraicSpace.EtaleTopos.allChartCone U
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
          ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W),
         AlgebraicSpace.EtaleTopos.allChartIsLimit U
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
          ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W)⟩).hom

/-- Sectionwise underlying comparison `(a_* H)|_{V_étale}(W) ⟶ a_small,* (H|_{U_étale})(W)`. -/
def restrictDirectImageComparisonUnderlying_app {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H))).obj.obj (op W) ⟶
      ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        (((AlgebraicSpace.ringedToposHom
            (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
          ((restrictModules eU).obj H))).obj.obj (op W) :=
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  (restrictDirectImageComparison_leftEval a eV H W).hom ≫
    ((sheafToPresheaf Vcfg.etaleTopology (Type u)).map
        ((RingedSite.ToposHom.ModulePushforward.forgetIso
            (etaleRingedToposHom a)).hom.app H)).app
      (op ((smallEtaleFunctor V Vcfg eV).obj W)) ≫
      restrictDirectImageComparison_rightEval a eU eV H W ≫
        ((sheafToPresheaf (AlgebraicSpace.smallEtaleTopology V) (Type u)).map
            ((RingedSite.ToposHom.ModulePushforward.forgetIso
                (AlgebraicSpace.ringedToposHom
                  (moduleComparisonSpaceMorphism a eU eV))).inv.app
              ((restrictModules eU).obj H))).app (op W)

/-- Identification `restrict(h_* H) ⟶ h_small,* (restrict H)` of restricted
direct images, as an underlying type-valued sheaf morphism. -/
def restrictDirectImageComparisonUnderlying {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf) :
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    (ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H)) ⟶
      (ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        (((AlgebraicSpace.ringedToposHom
            (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
          ((restrictModules eU).obj H)) :=
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  CategoryTheory.ObjectProperty.homMk
    { app := fun W => restrictDirectImageComparisonUnderlying_app a eU eV H W.unop
      naturality := sorry }

/-- Restriction of CFG direct image compared with small étale pushforward of the
restriction. -/
def restrictDirectImageComparison {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf) :
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    (restrictModules eV).obj ((etaleModuleDirectImage a).obj H) ⟶
      ((AlgebraicSpace.ringedToposHom
          (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
        ((restrictModules eU).obj H) :=
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  homOfUnderlying (AlgebraicSpace.structureSheaf V)
    (restrictDirectImageComparisonUnderlying a eU eV H) sorry sorry

/-- Comparison `a_small^*(G |_{V_étale}) ⟶ (a^* G)|_{U_étale}` of restricted
module sheaves on `U_étale`, the mate of the restricted CFG unit. -/
def restrictPullbackComparison {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (G : SheafOfModules.{u} (etaleRingedSite Vcfg).structureSheaf) :
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj G) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage a).obj G) :=
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
      ((restrictModules eV).obj G)
      ((restrictModules eU).obj ((etaleModuleInverseImage a).obj G))).symm
    ((restrictModules eV).map
        (etaleModuleUnit a G) ≫
      restrictDirectImageComparison a eU eV ((etaleModuleInverseImage a).obj G))

/-- The restricted 2-cell `(a^* g^* F)|_{U_étale} ⟶ (f^* F)|_{U_étale}`. -/
def restrictTwoCell {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (restrictModules eU).obj
        ((etaleModuleInverseImage a).obj ((etaleModuleInverseImage g).obj F)) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage f).obj F) :=
  (restrictModules eU).map ((etaleModuleInverseImage_twoCell a f g φ).hom.app F)

/-- Unit of the small-étale module adjunction of the space morphism corresponding
to `a`, applied to a restricted sheaf on `V`. -/
def moduleComparisonSpaceUnit {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (N : SheafOfModules.{u} (AlgebraicSpace.structureSheaf V)) :
    N ⟶
      ((AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
        ((AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj N) :=
  (AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).unit.app N

/-- The push-form comparison
`g^* F |_{V_étale} ⟶ a_small,* (f^* F |_{U_étale})` of `𝒪_{V_étale}`-modules:
the restricted unit of `a^* ⊣ a_*`, transported along `φ` and followed by
the direct-image comparison. -/
def moduleComparisonSpacePushforward {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (restrictModules eV).obj ((etaleModuleInverseImage g).obj F) ⟶
      ((AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
        ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F)) :=
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  (restrictModules eV).map
      (etaleModuleUnit a ((etaleModuleInverseImage g).obj F) ≫
        (etaleModuleDirectImage a).map
          ((etaleModuleInverseImage_twoCell a f g φ).hom.app F)) ≫
    restrictDirectImageComparison a eU eV ((etaleModuleInverseImage f).obj F)

/-- The comparison morphism
`c_φ : a_small^*(g^* F |_{V_étale}) ⟶ f^* F |_{U_étale}` of
`𝒪_{U_étale}`-modules, obtained as the adjunct of
`moduleComparisonSpacePushforward`. -/
def moduleComparisonSpace {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F)) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage f).obj F) :=
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
      ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F))
      ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F))).symm
    (moduleComparisonSpacePushforward a f g φ eU eV F)

/-- `moduleComparisonSpace` is the adjunct of `moduleComparisonSpacePushforward`
along the small-étale module adjunction of `a`. -/
theorem moduleComparisonSpace_adjunct {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
        ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F))
        ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F))
        (moduleComparisonSpace a f g φ eU eV F) =
      moduleComparisonSpacePushforward a f g φ eU eV F :=
  sorry

/-- Source-semantic characterisation: the push-form of `c_φ` is the restricted
unit of `a^* ⊣ a_*`, transported along `φ` and followed by the direct-image comparison. -/
theorem moduleComparisonSpace_spec {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    moduleComparisonSpacePushforward a f g φ eU eV F =
      (restrictModules eV).map
          (etaleModuleUnit a ((etaleModuleInverseImage g).obj F) ≫
            (etaleModuleDirectImage a).map
              ((etaleModuleInverseImage_twoCell a f g φ).hom.app F)) ≫
        restrictDirectImageComparison a eU eV
          ((etaleModuleInverseImage f).obj F) :=
  sorry

/-- Unfolding `moduleComparisonSpace` as the adjunct of the push form. -/
theorem moduleComparisonSpace_app {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    moduleComparisonSpace a f g φ eU eV F =
      ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
          ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F))
          ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F))).symm
        (moduleComparisonSpacePushforward a f g φ eU eV F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
