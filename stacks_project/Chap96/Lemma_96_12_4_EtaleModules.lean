module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.SliceEquivalence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CoefficientEquivalence
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Lemma_96_9_1_Localizing

/-!
# Étale modules on a category fibred in groupoids

A category fibred in groupoids `X` over `(Sch/S)_fppf` carries the associated étale
ringed site `(X_étale, 𝒪_X)`, obtained by pulling back the big étale structure sheaf
along the projection. Restriction of an étale module to the small étale site of the
scheme underlying an object of `X` is the composite of slice localization, transport
to `(Sch/U)_étale`, and restriction along `U_étale → (Sch/U)_étale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- Weak sheafification exists on every slice of the small étale topology. -/
instance over_hasWeakSheafify (U : Scheme.{u}) (V : U.Etale) :
    HasWeakSheafify (U.smallEtaleTopology.over V) AddCommGrpCat.{u} := sorry

/-- Sheafification equivalences on every small-étale slice are the locally bijective
morphisms. -/
instance over_wEqualsLocallyBijective (U : Scheme.{u}) (V : U.Etale) :
    (U.smallEtaleTopology.over V).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Ring-to-abelian-group sheaf composition exists on every small-étale slice. -/
instance over_hasSheafCompose_ring_addCommGrp (U : Scheme.{u}) (V : U.Etale) :
    (U.smallEtaleTopology.over V).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) := sorry

/-- Weak sheafification exists in universe `u + 1` on every small-étale slice. -/
instance over_hasWeakSheafify_succ (U : Scheme.{u}) (V : U.Etale) :
    HasWeakSheafify (U.smallEtaleTopology.over V) AddCommGrpCat.{u + 1} := sorry

/-- Sheafification equivalences in universe `u + 1` on every small-étale slice are the
locally bijective morphisms. -/
instance over_wEqualsLocallyBijective_succ (U : Scheme.{u}) (V : U.Etale) :
    (U.smallEtaleTopology.over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := sorry

/-- Ring-to-abelian-group sheaf composition exists in universe `u + 1` on every
small-étale slice. -/
instance over_hasSheafCompose_ring_addCommGrp_succ (U : Scheme.{u}) (V : U.Etale) :
    (U.smallEtaleTopology.over V).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := sorry

end AlgebraicGeometry.Scheme.Etale.Small

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Abelian-group-valued weak sheafification exists on the associated étale site. -/
instance etaleTopology_hasWeakSheafify (X : GroupoidsOver S) :
    HasWeakSheafify X.etaleTopology AddCommGrpCat.{u} := sorry

/-- On the associated étale site, sheafification equivalences are the locally bijective
morphisms. -/
instance etaleTopology_wEqualsLocallyBijective (X : GroupoidsOver S) :
    X.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Ring-to-abelian-group sheaf composition exists on the associated étale topology. -/
instance etaleTopology_hasSheafCompose_ring_addCommGrp (X : GroupoidsOver S) :
    X.etaleTopology.HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) := sorry

/-- Commutative-ring-to-ring sheaf composition exists on the associated étale topology. -/
instance etaleTopology_hasSheafCompose_commRing (X : GroupoidsOver S) :
    X.etaleTopology.HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) := sorry

/-- Abelian-group-valued sheaf composition exists in universe `u + 1` on the associated
étale topology. -/
instance etaleTopology_hasSheafCompose_addCommGrp_succ (X : GroupoidsOver S) :
    X.etaleTopology.HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := sorry

/-- Abelian-group-valued weak sheafification exists in universe `u + 1` on the associated
étale topology. -/
instance etaleTopology_hasWeakSheafify_succ (X : GroupoidsOver S) :
    HasWeakSheafify X.etaleTopology AddCommGrpCat.{u + 1} := sorry

/-- On the associated étale topology, sheafification equivalences in universe `u + 1` are the
locally bijective morphisms. -/
instance etaleTopology_wEqualsLocallyBijective_succ (X : GroupoidsOver S) :
    X.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := sorry

/-- The commutative global-sections presheaf on the big étale site of `S` is a sheaf. -/
theorem bigEtale_commStructurePresheaf_isSheaf :
    Presheaf.IsSheaf (StandardTopology.etale.overTopology S)
      ((Over.forget S).op ⋙ Scheme.Γ) := sorry

/-- The commutative structure sheaf on the big étale site of `S`. -/
def bigEtaleCommStructureSheaf :
    Sheaf (StandardTopology.etale.overTopology S) CommRingCat.{u} :=
  ⟨(Over.forget S).op ⋙ Scheme.Γ, bigEtale_commStructurePresheaf_isSheaf⟩

/-- The commutative structure sheaf `𝒪_X` on the associated étale site, obtained as the
inverse image `p⁻¹ 𝒪` of the big étale commutative structure sheaf. -/
def commEtaleStructureSheaf (X : GroupoidsOver S) :
    Sheaf X.etaleTopology CommRingCat.{u} :=
  (X.p.sheafPushforwardContinuous CommRingCat.{u}
      X.etaleTopology (StandardTopology.etale.overTopology S)).obj
    bigEtaleCommStructureSheaf

/-- `commEtaleStructureSheaf` is the continuous pushforward of the big étale commutative
structure sheaf along the projection of `X`. -/
theorem commEtaleStructureSheaf_def (X : GroupoidsOver S) :
    commEtaleStructureSheaf X =
      (X.p.sheafPushforwardContinuous CommRingCat.{u}
          X.etaleTopology (StandardTopology.etale.overTopology S)).obj
        bigEtaleCommStructureSheaf := sorry

/-- The étale ringed site of `X`, with commutative structure sheaf `𝒪_X`. -/
abbrev etaleRingedSite (X : GroupoidsOver S) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofCommRingSheaf X.etaleTopology (commEtaleStructureSheaf X)

/-- The structure sheaf `𝒪_X` on the associated étale site, as a sheaf of rings. -/
abbrev etaleStructureSheaf (X : GroupoidsOver S) :
    Sheaf X.etaleTopology RingCat.{u} :=
  (etaleRingedSite X).structureSheaf

/-- The ring-valued étale structure sheaf is the structure sheaf of `etaleRingedSite X`. -/
theorem etaleStructureSheaf_eq (X : GroupoidsOver S) :
    etaleStructureSheaf X = (etaleRingedSite X).structureSheaf := sorry

/-- The étale structure sheaf agrees with the continuous pushforward of the big étale
structure sheaf along the projection of `X`. -/
theorem etaleStructureSheaf_eq_pushforward (X : GroupoidsOver S) :
    etaleStructureSheaf X =
      (X.p.sheafPushforwardContinuous RingCat.{u}
          X.etaleTopology (StandardTopology.etale.overTopology S)).obj
        (StandardTopology.Big.structureSheaf .etale S) := sorry

/-- The structure sheaf of `etaleRingedSite X` is the ring sheaf underlying `𝒪_X`. -/
theorem etaleRingedSite_structureSheaf (X : GroupoidsOver S) :
    (etaleRingedSite X).structureSheaf = etaleStructureSheaf X := sorry

/-- The commutative étale ringed site of `X` is the étale ringed site. -/
abbrev commEtaleRingedSite (X : GroupoidsOver S) : RingedSite.{u + 1, u, u} :=
  etaleRingedSite X

/-- The structure sheaf of `commEtaleRingedSite X` is the ring sheaf underlying `𝒪_X`. -/
theorem commEtaleRingedSite_structureSheaf (X : GroupoidsOver S) :
    (commEtaleRingedSite X).structureSheaf = etaleStructureSheaf X := sorry

/-- The category of sheaves of modules on `(X_étale, 𝒪_X)`. -/
abbrev etaleModules (X : GroupoidsOver S) :=
  RingedSite.ModuleCat.{u} (etaleRingedSite X)

/-- The category of étale `𝒪_X`-modules is abelian. -/
instance etaleModulesAbelian (X : GroupoidsOver S) : Abelian (etaleModules X) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The étale module category has colimits of every universe-compatible shape. -/
instance etaleModules_hasColimitsOfShape (X : GroupoidsOver S)
    (J : Type v) [Category.{w} J] :
    HasColimitsOfShape J (etaleModules X) := sorry

/-- The universe lift of the commutative étale structure presheaf. -/
abbrev commEtaleStructurePresheafLift (X : GroupoidsOver S) :
    X.totalᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (commEtaleStructureSheaf X).obj ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The lifted commutative étale structure presheaf is a sheaf. -/
theorem commEtaleStructurePresheafLift_isSheaf (X : GroupoidsOver S) :
    Presheaf.IsSheaf X.etaleTopology (commEtaleStructurePresheafLift X) := sorry

/-- The universe-lifted commutative structure sheaf on the associated étale site. -/
def commEtaleStructureSheafLift (X : GroupoidsOver S) :
    Sheaf X.etaleTopology CommRingCat.{u + 1} :=
  ⟨commEtaleStructurePresheafLift X, commEtaleStructurePresheafLift_isSheaf X⟩

/-- The associated étale site equipped with the universe-lifted commutative structure sheaf. -/
abbrev commEtaleRingedSiteLift (X : GroupoidsOver S) : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommSheafMax X.etaleTopology (commEtaleStructureSheafLift X)

/-- The structure sheaf of `commEtaleRingedSiteLift X` is the underlying ring sheaf of the
lifted commutative structure sheaf. -/
theorem commEtaleRingedSiteLift_structureSheaf (X : GroupoidsOver S) :
    (commEtaleRingedSiteLift X).structureSheaf =
      CategoryTheory.Sheaf.ringSheafOfComm (commEtaleStructureSheafLift X) := sorry

/-- Identity-on-schemes comparison from the realization of `overPostScheme p x` to
`Over.forget x ⋙ p ⋙ Over.forget S`. -/
def overPostSchemeSchemeProjection (X : GroupoidsOver S) (x : X.total) :
    overPostScheme X.p x ⋙ Over.forget (X.p.obj x).left ⟶
      Over.forget x ⋙ X.p ⋙ Over.forget S where
  app _ := 𝟙 _
  naturality := sorry

/-- `overPostSchemeSchemeProjection` is objectwise the identity of the underlying scheme. -/
theorem overPostSchemeSchemeProjection_app (X : GroupoidsOver S) (x : X.total)
    (y : Over x) :
    (overPostSchemeSchemeProjection X x).app y = 𝟙 _ := sorry

/-- `overPostScheme` is continuous from the localized étale site of `X` at `x` to
`(Sch/U)_étale`. -/
instance overPostScheme_isContinuous_etale (X : GroupoidsOver S) (x : X.total) :
    (overPostScheme X.p x).IsContinuous
      ((etaleRingedSite X).localization x).siteTopology
      (StandardTopology.etale.overTopology (X.p.obj x).left) :=
  (overPostScheme.isMorphismOfSites X.p x .etale).toIsContinuous

/-- `overPostScheme` is continuous from the localized lifted étale site of `X` at `x`
to `(Sch/U)_étale`. -/
instance overPostScheme_isContinuous_etaleLift (X : GroupoidsOver S) (x : X.total) :
    (overPostScheme X.p x).IsContinuous
      ((commEtaleRingedSiteLift X).localization x).siteTopology
      (StandardTopology.etale.overTopology (X.p.obj x).left) :=
  (overPostScheme.isMorphismOfSites X.p x .etale).toIsContinuous

/-- Unfolding of étale `𝒪_X` as `p.op ⋙ ((Over.forget S).op ⋙ Γ)`, then `forget₂`. -/
def etaleStructureSheafToPushforward (X : GroupoidsOver S) :
    (etaleStructureSheaf X).obj ≅
      (X.p.op ⋙ bigEtaleCommStructureSheaf.obj) ⋙
        forget₂ CommRingCat.{u} RingCat.{u} :=
  isoWhiskerRight
    ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
        X.etaleTopology (StandardTopology.etale.overTopology S)).app
      bigEtaleCommStructureSheaf)
    (forget₂ CommRingCat.{u} RingCat.{u})

/-- `etaleStructureSheafToPushforward` is whiskering of the continuous-pushforward
identification by `forget₂`. -/
theorem etaleStructureSheafToPushforward_eq (X : GroupoidsOver S) :
    etaleStructureSheafToPushforward X =
      isoWhiskerRight
        ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
            X.etaleTopology (StandardTopology.etale.overTopology S)).app
          bigEtaleCommStructureSheaf)
        (forget₂ CommRingCat.{u} RingCat.{u}) := sorry

/-- Reassociation identifying the slice of étale `𝒪_X` at `x` with the
global-sections presheaf of `Over.forget x ⋙ X.p ⋙ Over.forget S`. -/
def localizationEtaleStructurePresheafIso (X : GroupoidsOver S) (x : X.total) :
    ((etaleRingedSite X).localization x).structureSheaf.obj ≅
      Scheme.Site.structurePresheaf (Over.forget x ⋙ X.p ⋙ Over.forget S) :=
  isoWhiskerLeft (Over.forget x).op (etaleStructureSheafToPushforward X) ≪≫
    (associator (Over.forget x).op (X.p.op ⋙ bigEtaleCommStructureSheaf.obj)
      (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
    isoWhiskerRight (associator (Over.forget x).op X.p.op
        bigEtaleCommStructureSheaf.obj).symm
      (forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    isoWhiskerRight
      (associator ((Over.forget x).op ⋙ X.p.op) (Over.forget S).op Scheme.Γ).symm
      (forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    associator (((Over.forget x).op ⋙ X.p.op) ⋙ (Over.forget S).op) Scheme.Γ
      (forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    isoWhiskerRight (associator (Over.forget x).op X.p.op (Over.forget S).op)
      (Scheme.Γ ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (Over.forget x).op ((X.p).opComp (Over.forget S)).symm)
      (Scheme.Γ ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    isoWhiskerRight ((Over.forget x).opComp (X.p ⋙ Over.forget S)).symm
      (Scheme.Γ ⋙ forget₂ CommRingCat.{u} RingCat.{u})

/-- Objectwise, `localizationEtaleStructurePresheafIso` identifies sections of the
slice of étale `𝒪_X` with global sections of the composite realization. -/
theorem localizationEtaleStructurePresheafIso_obj
    (X : GroupoidsOver S) (x : X.total) (y : Over x) :
    ((etaleRingedSite X).localization x).structureSheaf.obj.obj (op y) =
      (Scheme.Site.structurePresheaf
        (Over.forget x ⋙ X.p ⋙ Over.forget S)).obj (op y) := sorry

/-- The comparison `(etaleStructureSheaf X).over x ⟶ (overPostScheme X.p x)_* 𝒪_{(Sch/U)_étale}`
induced by global sections of `overPostSchemeSchemeProjection`, after reassociating the
slice sheaf to that composite's global-sections presheaf. -/
noncomputable def localizationToBigEtaleStructureSheafMap
    (X : GroupoidsOver S) (x : X.total) :
    ((etaleRingedSite X).localization x).structureSheaf ⟶
      ((overPostScheme X.p x).sheafPushforwardContinuous RingCat.{u}
          ((etaleRingedSite X).localization x).siteTopology
          (StandardTopology.etale.overTopology (X.p.obj x).left)).obj
        (StandardTopology.Big.structureSheaf .etale (X.p.obj x).left) :=
  { hom :=
      (localizationEtaleStructurePresheafIso X x).hom ≫
        Scheme.Site.structurePresheafMap
          (Over.forget x ⋙ X.p ⋙ Over.forget S)
          (Over.forget (X.p.obj x).left)
          (overPostScheme X.p x)
          (overPostSchemeSchemeProjection X x) }

/-- `localizationToBigEtaleStructureSheafMap` is the reassociating iso followed by the
global-sections map of `overPostSchemeSchemeProjection`. -/
theorem localizationToBigEtaleStructureSheafMap_hom
    (X : GroupoidsOver S) (x : X.total) :
    (localizationToBigEtaleStructureSheafMap X x).hom =
      (localizationEtaleStructurePresheafIso X x).hom ≫
        Scheme.Site.structurePresheafMap
          (Over.forget x ⋙ X.p ⋙ Over.forget S)
          (Over.forget (X.p.obj x).left)
          (overPostScheme X.p x)
          (overPostSchemeSchemeProjection X x) := sorry

/-- The morphism of ringed sites from the localized étale site of `X` at `x` to the big
étale site of `U = p(x)`, with base functor `overPostScheme X.p x`. -/
noncomputable def localizationToBigEtale (X : GroupoidsOver S) (x : X.total) :
    RingedSite.Hom
      (StandardTopology.Big.ringedSite .etale (X.p.obj x).left)
      ((etaleRingedSite X).localization x) where
  base := overPostScheme X.p x
  isMorphismOfSites := overPostScheme.isMorphismOfSites X.p x .etale
  structureSheafMap := localizationToBigEtaleStructureSheafMap X x

/-- The base functor of `localizationToBigEtale` is `overPostScheme` of the projection. -/
theorem localizationToBigEtale_base (X : GroupoidsOver S) (x : X.total) :
    (localizationToBigEtale X x).base = overPostScheme X.p x := sorry

/-- The structure-sheaf map of `localizationToBigEtale` is
`localizationToBigEtaleStructureSheafMap`. -/
theorem localizationToBigEtale_structureSheafMap (X : GroupoidsOver S) (x : X.total) :
    (localizationToBigEtale X x).structureSheafMap =
      localizationToBigEtaleStructureSheafMap X x := sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.GroupoidsOver.LocalizationGeometry
open AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}} (X : GroupoidsOver S) (x : X.total)

/-- The base equivalence uses the proved Cartesian slice equivalence and the
actual iterated-slice functors. -/
def siteEquivalence : Over x ≌ Over (X.p.obj x).left :=
  (CategoryTheory.FiberedSliceEquivalence.equivalence X.p x).trans (X.p.obj x).iteratedSliceEquiv

@[simp]
theorem siteEquivalence_functor : (siteEquivalence X x).functor = overPostScheme X.p x := rfl

/-- The inherited topology law applies to this fixed equivalence functor. -/
instance forwardDense : (siteEquivalence X x).functor.IsDenseSubsite
    ((etaleRingedSite X).localization x).siteTopology
    (StandardTopology.etale.overTopology (X.p.obj x).left) :=
  overPostScheme.isDenseSubsite X.p x .etale

instance backwardDense : (siteEquivalence X x).inverse.IsDenseSubsite
    (StandardTopology.etale.overTopology (X.p.obj x).left)
    ((etaleRingedSite X).localization x).siteTopology := by
  let e := (siteEquivalence X x).symm
  -- Local instance justification (defeq pin): the inverse of the reversed site equivalence is the already proved dense forward functor.
  letI : e.inverse.IsDenseSubsite ((etaleRingedSite X).localization x).siteTopology
      (StandardTopology.etale.overTopology (X.p.obj x).left) := forwardDense X x
  change e.functor.IsDenseSubsite _ _
  rw [e.eq_inducedTopology_of_isDenseSubsite
    (StandardTopology.etale.overTopology (X.p.obj x).left)
    ((etaleRingedSite X).localization x).siteTopology]
  infer_instance

/-- The scheme projection and its inverse are the identity on underlying schemes. -/
def projectionIso : overPostScheme X.p x ⋙ Over.forget (X.p.obj x).left ≅
    Over.forget x ⋙ X.p ⋙ Over.forget S :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => (overPostSchemeSchemeProjection X x).naturality f)

/-- Reassociation and the actual global-sections functor give both coefficient maps. -/
def coefficientPresheafIso :
    ((etaleRingedSite X).localization x).structureSheaf.obj ≅
      (overPostScheme X.p x).op ⋙ (StandardTopology.Big.structureSheaf .etale (X.p.obj x).left).obj :=
  localizationEtaleStructurePresheafIso X x ≪≫
    isoWhiskerRight (NatIso.op (projectionIso X x)).symm (Scheme.Γ ⋙ forget₂ CommRingCat RingCat)

/-- The explicit presheaf isomorphism lifts along the fully faithful sheaf forgetful functor. -/
def coefficientIso :
    ((etaleRingedSite X).localization x).structureSheaf ≅
      ((siteEquivalence X x).functor.sheafPushforwardContinuous RingCat.{u}
        ((etaleRingedSite X).localization x).siteTopology
        (StandardTopology.etale.overTopology (X.p.obj x).left)).obj
        (StandardTopology.Big.structureSheaf .etale (X.p.obj x).left) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (coefficientPresheafIso X x)

/-- The constructed forward coefficient map is definitionally the original one. -/
theorem coefficientIso_hom : (coefficientIso X x).hom =
    localizationToBigEtaleStructureSheafMap X x := by
  apply (fullyFaithfulSheafToPresheaf _ _).map_injective
  apply NatTrans.ext
  funext U
  rfl

end AlgebraicGeometry.GroupoidsOver.LocalizationGeometry

namespace AlgebraicGeometry.GroupoidsOver.LocalizationAdjunction
open AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}} (X : GroupoidsOver S) (x : X.total)

/-- The left adjoint is reverse pushforward with the actual inverse coefficient map. -/
def left : RingedSite.ModuleCat.{u} ((etaleRingedSite X).localization x) ⥤
    RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite .etale (X.p.obj x).left) :=
  SheafOfModules.pushforward.{u}
    (SheafOfModules.CoefficientEquivalence.reverse (LocalizationGeometry.siteEquivalence X x)
      (LocalizationGeometry.coefficientIso X x))

/-- The constructed module equivalence supplies the exact original right functor. -/
def adjunction : left X x ⊣ (localizationToBigEtale X x).modulePushforward.{u} := by
  have h := SheafOfModules.CoefficientEquivalence.adjunction (LocalizationGeometry.siteEquivalence X x)
    (LocalizationGeometry.coefficientIso X x)
  rw [LocalizationGeometry.coefficientIso_hom] at h
  exact h

/-- Existence is witnessed by the displayed concrete left adjoint. -/
theorem certificate : ((localizationToBigEtale X x).modulePushforward.{u}).IsRightAdjoint :=
  (adjunction X x).isRightAdjoint

end AlgebraicGeometry.GroupoidsOver.LocalizationAdjunction

namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}

/-- Module pushforward along `localizationToBigEtale` has the concrete inverse-pushforward left adjoint. -/
instance localizationToBigEtale_modulePushforward_isRightAdjoint
    (X : GroupoidsOver S) (x : X.total) :
    ((localizationToBigEtale X x).modulePushforward.{u}).IsRightAdjoint :=
  AlgebraicGeometry.GroupoidsOver.LocalizationAdjunction.certificate X x

/-- The étale standard topology is distinct from the Zariski topology. -/
theorem etale_ne_zariski : StandardTopology.etale ≠ StandardTopology.zariski := sorry

/-- The small-étale forgetful functor is continuous into the big étale site. -/
instance smallEtaleForget_isContinuous_etale (U : Scheme.{u}) :
    (Scheme.Etale.forget U).IsContinuous U.smallEtaleTopology
      (StandardTopology.etale.overTopology U) :=
  Scheme.SiteRestriction.smallEtaleForget_isContinuous .etale U etale_ne_zariski

/-- Restriction of étale `𝒪_X`-modules to the small étale site of `U = p(x)`, as the
composite of slice localization, inverse image to `(Sch/U)_étale`, and direct image
along `U_étale → (Sch/U)_étale`. -/
noncomputable def restrictModulesToSmallEtale (X : GroupoidsOver S) (x : X.total) :
    etaleModules X ⥤
      RingedSite.ModuleCat.{u}
        (Scheme.Etale.Small.ringedSite (X.p.obj x).left) :=
  RingedSite.Hom.localizedRestriction (etaleRingedSite X) x ⋙
    (localizationToBigEtale X x).modulePullback.{u} ⋙
      (Scheme.SiteRestriction.bigToEtale .etale (X.p.obj x).left
        etale_ne_zariski).modulePushforward.{u}

/-- Restriction to the small étale site is localization followed by transport to the big
étale site of `U` and pushforward to `U_étale`. -/
theorem restrictModulesToSmallEtale_comp (X : GroupoidsOver S) (x : X.total) :
    restrictModulesToSmallEtale X x =
      RingedSite.Hom.localizedRestriction (etaleRingedSite X) x ⋙
        (localizationToBigEtale X x).modulePullback.{u} ⋙
          (Scheme.SiteRestriction.bigToEtale .etale (X.p.obj x).left
            etale_ne_zariski).modulePushforward.{u} := sorry

/-- Universe lift of `localizationToBigEtaleStructureSheafMap` along `ringUniverseLift`. -/
noncomputable def localizationToBigEtaleStructureSheafMapLift
    (X : GroupoidsOver S) (x : X.total) :
    ((commEtaleRingedSiteLift X).localization x).structureSheaf ⟶
      ((overPostScheme X.p x).sheafPushforwardContinuous RingCat.{u + 1}
          ((commEtaleRingedSiteLift X).localization x).siteTopology
          (StandardTopology.etale.overTopology (X.p.obj x).left)).obj
        (StandardTopology.Big.liftedStructureSheaf .etale (X.p.obj x).left) :=
  { hom :=
      whiskerRight (localizationToBigEtaleStructureSheafMap X x).hom
        Scheme.Site.ringUniverseLift.{u, u + 1} }

/-- `localizationToBigEtaleStructureSheafMapLift` is the universe lift of
`localizationToBigEtaleStructureSheafMap`. -/
theorem localizationToBigEtaleStructureSheafMapLift_hom
    (X : GroupoidsOver S) (x : X.total) :
    (localizationToBigEtaleStructureSheafMapLift X x).hom =
      whiskerRight (localizationToBigEtaleStructureSheafMap X x).hom
        Scheme.Site.ringUniverseLift.{u, u + 1} := sorry

/-- The morphism of ringed sites from the localized lifted étale site of `X` at `x` to the
lifted big étale site of `U = p(x)`. -/
noncomputable def localizationToBigEtaleLift (X : GroupoidsOver S) (x : X.total) :
    RingedSite.Hom
      (StandardTopology.Big.liftedRingedSite .etale (X.p.obj x).left)
      ((commEtaleRingedSiteLift X).localization x) where
  base := overPostScheme X.p x
  isMorphismOfSites := overPostScheme.isMorphismOfSites X.p x .etale
  structureSheafMap := localizationToBigEtaleStructureSheafMapLift X x

/-- Module pushforward along `localizationToBigEtaleLift` admits its canonical left adjoint. -/
instance localizationToBigEtaleLift_modulePushforward_isRightAdjoint
    (X : GroupoidsOver S) (x : X.total) :
    ((localizationToBigEtaleLift X x).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- Universe lift of the structure-sheaf map of `Scheme.SiteRestriction.bigToEtale`. -/
noncomputable def bigToSmallEtaleLiftStructureSheafMap (U : Scheme.{u}) :
    (Scheme.Etale.Small.liftedRingedSite U).structureSheaf ⟶
      ((Scheme.Etale.forget U).sheafPushforwardContinuous RingCat.{u + 1}
          U.smallEtaleTopology (StandardTopology.etale.overTopology U)).obj
        (StandardTopology.Big.liftedStructureSheaf .etale U) :=
  { hom :=
      whiskerRight
        (Scheme.SiteRestriction.bigToEtale .etale U etale_ne_zariski).structureSheafMap.hom
        Scheme.Site.ringUniverseLift.{u, u + 1} }

/-- `bigToSmallEtaleLiftStructureSheafMap` is the universe lift of the unlifted
`bigToEtale` structure-sheaf map. -/
theorem bigToSmallEtaleLiftStructureSheafMap_hom (U : Scheme.{u}) :
    (bigToSmallEtaleLiftStructureSheafMap U).hom =
      whiskerRight
        (Scheme.SiteRestriction.bigToEtale .etale U etale_ne_zariski).structureSheafMap.hom
        Scheme.Site.ringUniverseLift.{u, u + 1} := sorry

/-- The lifted ringed-site morphism from the big étale site of `U` to the small étale site. -/
noncomputable def bigToSmallEtaleLift (U : Scheme.{u}) :
    RingedSite.Hom
      (StandardTopology.Big.liftedRingedSite .etale U)
      (Scheme.Etale.Small.liftedRingedSite U) where
  base := Scheme.Etale.forget U
  isMorphismOfSites :=
    Scheme.SiteRestriction.smallEtaleForget_isMorphismOfSites .etale U etale_ne_zariski
  structureSheafMap := bigToSmallEtaleLiftStructureSheafMap U

/-- Module pushforward along `bigToSmallEtaleLift` admits its canonical left adjoint. -/
instance bigToSmallEtaleLift_modulePushforward_isRightAdjoint (U : Scheme.{u}) :
    ((bigToSmallEtaleLift U).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- Restriction of lifted étale modules to the lifted small étale site of `U = p(x)`. -/
noncomputable def restrictToSmallEtaleLift (X : GroupoidsOver S) (x : X.total) :
    RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) ⥤
      RingedSite.ModuleCat.{u + 1}
        (Scheme.Etale.Small.liftedRingedSite (X.p.obj x).left) :=
  RingedSite.Hom.localizedRestriction.{u + 1} (commEtaleRingedSiteLift X) x ⋙
    (localizationToBigEtaleLift X x).modulePullback.{u + 1} ⋙
      (bigToSmallEtaleLift (X.p.obj x).left).modulePushforward.{u + 1}

/-- Lifted restriction is localization followed by the lifted comparison to `(Sch/U)_étale`
and pushforward to the lifted small étale site. -/
theorem restrictToSmallEtaleLift_comp (X : GroupoidsOver S) (x : X.total) :
    restrictToSmallEtaleLift X x =
      RingedSite.Hom.localizedRestriction.{u + 1} (commEtaleRingedSiteLift X) x ⋙
        (localizationToBigEtaleLift X x).modulePullback.{u + 1} ⋙
          (bigToSmallEtaleLift (X.p.obj x).left).modulePushforward.{u + 1} := sorry

end AlgebraicGeometry.GroupoidsOver
