module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Coproduct
public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Finite colimits of finite étale schemes

Finite coproducts are the actual disjoint unions of schemes. The coequalizer
of `a, b : Z ⟶ Y` is obtained by gluing spectra of the literal equalizer
subrings of the section maps on affine opens of the base. Its quotient map
and its universal descent maps are constructed on those same charts.

The affine transition pullbacks use the native flat base-change theorem for
ring equalizers. Their universal lifts have actual data; only commutation,
finiteness, étaleness and the universal-property laws may be deferred.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X : Scheme.{u}}

section Coproducts

variable {ι : Type u} [Finite ι] (Y : ι → FiniteEtale X)

/-- The finite disjoint union, with its actual structural morphism. -/
def coproduct : FiniteEtale X :=
  MorphismProperty.Over.mk _ (Sigma.desc (fun i ↦ (Y i).hom))
    ⟨finite_sigma_desc _ (fun i ↦ (Y i).prop.1),
      IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun i ↦ (Y i).prop.2)⟩

/-- The inclusions of the actual scheme disjoint union. -/
def coproductι (i : ι) : Y i ⟶ coproduct Y :=
  MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (Y i).left) i) sorry

/-- Descend a finite family of maps by the native scheme coproduct operation. -/
def coproductDesc {W : FiniteEtale X} (f : ∀ i, Y i ⟶ W) : coproduct Y ⟶ W :=
  MorphismProperty.Over.homMk (Sigma.desc (fun i ↦ (f i).left)) sorry

/-- The actual finite coproduct cocone. -/
def coproductCofan : Cofan Y :=
  Cofan.mk (coproduct Y) (coproductι Y)

/-- The universal desc is the native disjoint-union desc. -/
def coproductIsColimit : IsColimit (coproductCofan Y) :=
  Cofan.IsColimit.mk _ (fun c ↦ coproductDesc Y c.inj) sorry sorry

/-- Finite étale schemes have finite coproducts given by disjoint unions. -/
instance hasFiniteCoproducts : HasFiniteCoproducts (FiniteEtale X) where
  out n :=
    { has_colimit := fun F ↦ by
        let family : ULift.{u} (Fin n) → FiniteEtale X := fun i ↦ F.obj ⟨i.down⟩
        let c : Cocone F :=
          { pt := coproduct family
            ι := { app := fun i ↦ coproductι family ⟨i.as⟩, naturality := sorry } }
        let hc : IsColimit c :=
          { desc := fun t ↦ coproductDesc family (fun i ↦ t.ι.app ⟨i.down⟩)
            fac := sorry
            uniq := sorry }
        exact ⟨⟨c, hc⟩⟩ }

end Coproducts

namespace Coequalizer

variable {Z Y : FiniteEtale X} (a b : Z ⟶ Y)

/-- The inverse-image open of a finite étale scheme above a base open. -/
abbrev preimage (W : FiniteEtale X) (U : X.Opens) : W.left.Opens :=
  W.hom ⁻¹ᵁ U

/-- Sections of the affine base open, in the native affine-scheme convention. -/
abbrev baseRing (U : X.Opens) : CommRingCat.{u} :=
  Γ((U : X.Opens).toScheme, ⊤)

/-- Sections above a base open, retaining the native affine scheme. -/
abbrev sectionRing (W : FiniteEtale X) (U : X.Opens) : CommRingCat.{u} :=
  Γ((preimage W U).toScheme, ⊤)

/-- An affine-open label supplies its given native affine inverse. -/
instance baseIsAffine (U : X.affineOpens) : IsAffine (U : X.Opens).toScheme := U.property

/-- The affine structural map to a base open. -/
abbrev structureMap (W : FiniteEtale X) (U : X.Opens) :
    (preimage W U).toScheme ⟶ (U : X.Opens).toScheme :=
  W.hom ∣_ U

/-- The section algebra above a base open. -/
def sectionAlgebra (W : FiniteEtale X) (U : X.Opens) : Under (baseRing U) :=
  Under.mk (structureMap W U).appTop

/-- Restrict a morphism over the base to its actual inverse-image opens. -/
def restrictHom {W W' : FiniteEtale X} (f : W ⟶ W') (U : X.Opens) :
    (preimage W U).toScheme ⟶ (preimage W' U).toScheme :=
  f.left.resLE (preimage W' U) (preimage W U) (by
    change W.hom ⁻¹ᵁ U ≤ (f.left ≫ W'.hom) ⁻¹ᵁ U
    rw [MorphismProperty.Over.w f]
    exact le_rfl)

/-- The induced section-algebra map; its underlying map is the actual restriction. -/
def sectionMap {W W' : FiniteEtale X} (f : W ⟶ W') (U : X.Opens) :
    sectionAlgebra W' U ⟶ sectionAlgebra W U :=
  Under.homMk (restrictHom f U).appTop sorry

/-- The literal equalizer algebra, with inherited ring operations and inclusion. -/
def algebra (U : X.Opens) : Under (baseRing U) :=
  (CommRingCat.Under.equalizerFork (sectionMap a U) (sectionMap b U)).pt

/-- The literal subring equalizer used for the quotient chart. -/
abbrev ring (U : X.Opens) : CommRingCat.{u} :=
  (algebra a b U).right

/-- Inclusion of the equalizer subring in the sections of `Y`. -/
def inclusion (U : X.Opens) : ring a b U ⟶ sectionRing Y U :=
  (CommRingCat.Under.equalizerFork (sectionMap a U) (sectionMap b U)).ι.right

/-- The native equalizer lift is restriction of a ring map to its equalizing values. -/
def algebraIsLimit (U : X.Opens) :
    IsLimit (CommRingCat.Under.equalizerFork (sectionMap a U) (sectionMap b U)) :=
  CommRingCat.Under.equalizerForkIsLimit _ _

/-- Restriction between the affine base section rings. -/
def baseRestrict {U V : X.Opens} (h : U ≤ V) : baseRing V ⟶ baseRing U :=
  (X.homOfLE h).appTop

/-- Restriction between the corresponding section rings above the base. -/
def sectionRestrict (W : FiniteEtale X) {U V : X.Opens} (h : U ≤ V) :
    sectionRing W V ⟶ sectionRing W U :=
  (W.left.homOfLE (W.hom.preimage_mono h)).appTop

/-- Restriction on equalizers is literally restriction on the underlying section. -/
def restrict {U V : X.Opens} (h : U ≤ V) : ring a b V ⟶ ring a b U :=
  CommRingCat.ofHom
    { toFun := fun s ↦ ⟨sectionRestrict Y h s.val, sorry⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Affineness above an affine base open comes from the supplied finite morphism. -/
instance preimageIsAffine (W : FiniteEtale X) (U : X.affineOpens) :
    IsAffine (preimage W U).toScheme :=
  @IsAffineHom.isAffine_preimage W.left X W.hom
    (W.prop.1 : IsFinite W.hom).toIsAffineHom (U : X.Opens) U.property

/-- The original finite morphism supplies the actual affine section pushout square. -/
theorem sectionPushout (W : FiniteEtale X) {U V : X.affineOpens} (h : U ≤ V) :
    IsPushout (sectionAlgebra W V).hom (baseRestrict h)
      (sectionRestrict W h) (sectionAlgebra W U).hom := by
  letI : IsAffine (U : X.Opens).toScheme := U.property
  letI : IsAffine (V : X.Opens).toScheme := V.property
  letI : IsAffineHom W.hom := (W.prop.1 : IsFinite W.hom).toIsAffineHom
  letI : IsAffine (W.hom ⁻¹ᵁ (U : X.Opens)).toScheme := preimageIsAffine W U
  letI : IsAffine (W.hom ⁻¹ᵁ (V : X.Opens)).toScheme := preimageIsAffine W V
  let square : IsPullback (structureMap W U)
      (W.left.homOfLE (W.hom.preimage_mono h))
      (X.homOfLE h) (structureMap W V) :=
    IsOpenImmersion.isPullback _ _ _ _ sorry sorry
  exact (@isPushout_appTop_of_isPullback
    (U : X.Opens).toScheme (preimage W V).toScheme (V : X.Opens).toScheme
    (preimage W U).toScheme (structureMap W U)
    (W.left.homOfLE (W.hom.preimage_mono h)) (X.homOfLE h) (structureMap W V)
    U.property (preimageIsAffine W V) V.property square).flip

/-- The section base-change isomorphism comes from the two actual pushout desc maps. -/
def sectionBaseChangeIso (W : FiniteEtale X) {U V : X.affineOpens} (h : U ≤ V) :
    (Under.pushout (baseRestrict h)).obj (sectionAlgebra W V) ≅ sectionAlgebra W U :=
  Under.isoMk (sectionPushout W h).isoPushout.symm sorry

/-- Flat base change preserves the equalizer with its native universal lift. -/
def baseChangedAlgebraIsLimit {U V : X.affineOpens} (h : U ≤ V) :
    IsLimit ((Under.pushout (baseRestrict h)).mapCone
      (CommRingCat.Under.equalizerFork (sectionMap a V) (sectionMap b V))) := by
  letI : IsAffine (U : X.Opens).toScheme := U.property
  letI : IsAffine (V : X.Opens).toScheme := V.property
  letI : PreservesFiniteLimits (Under.pushout (baseRestrict h)) :=
    CommRingCat.Under.preservesFiniteLimits_of_flat _ (X.homOfLE h).flat_appTop
  exact isLimitOfPreserves _ (algebraIsLimit a b V)

/-- Actual affine section base change identifies the two parallel-arrow diagrams. -/
def baseChangedDiagramIso {U V : X.affineOpens} (h : U ≤ V) :
    parallelPair (sectionMap a V) (sectionMap b V) ⋙ Under.pushout (baseRestrict h) ≅
      parallelPair (sectionMap a U) (sectionMap b U) :=
  parallelPairIsoMk (sectionBaseChangeIso Y h) (sectionBaseChangeIso Z h) sorry sorry

/-- Both directions use actual equalizer lifts and actual section base-change isomorphisms. -/
def algebraBaseChangeIso {U V : X.affineOpens} (h : U ≤ V) :
    (Under.pushout (baseRestrict h)).obj (algebra a b V) ≅ algebra a b U :=
  IsLimit.conePointsIsoOfNatIso (baseChangedAlgebraIsLimit a b h)
    (algebraIsLimit a b U) (baseChangedDiagramIso a b h)

/-- The underlying actual ring isomorphism for equalizer base change. -/
def ringBaseChangeIso {U V : X.affineOpens} (h : U ≤ V) :
    pushout (algebra a b V).hom (baseRestrict h) ≅ ring a b U :=
  (Under.forget _).mapIso (algebraBaseChangeIso a b h)

/-- The equalizer restriction square has actual pushout desc data. -/
theorem algebraPushout {U V : X.affineOpens} (h : U ≤ V) :
    IsPushout (algebra a b V).hom (baseRestrict h)
      (restrict a b h) (algebra a b U).hom :=
  (IsPushout.of_hasPushout (algebra a b V).hom (baseRestrict h)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (ringBaseChangeIso a b h)
    rfl rfl sorry sorry

/-- The affine quotient transition square carries the concrete native pullback lift. -/
theorem chartPullback {U V : X.affineOpens} (h : U ≤ V) :
    IsPullback (Spec.map (restrict a b h))
      (Spec.map (algebra a b U).hom ≫ (U : X.Opens).toScheme.isoSpec.inv)
      (Spec.map (algebra a b V).hom ≫ (V : X.Opens).toScheme.isoSpec.inv) (X.homOfLE h) := by
  letI : IsAffine (U : X.Opens).toScheme := U.property
  letI : IsAffine (V : X.Opens).toScheme := V.property
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ (algebraPushout a b h)).of_iso
    (Iso.refl _) (Iso.refl _) (U : X.Opens).toScheme.isoSpec.symm (V : X.Opens).toScheme.isoSpec.symm
    rfl rfl sorry sorry

/-- The spectra of the literal equalizer rings, glued with actual transition lifts. -/
def gluingData : X.directedAffineCover.RelativeGluingData where
  functor :=
    { obj := fun (U : X.affineOpens) ↦ Spec (ring a b (U : X.Opens))
      map := fun {U V : X.affineOpens} h ↦ Spec.map (restrict a b (leOfHom h))
      map_id := sorry
      map_comp := sorry }
  natTrans :=
    { app := fun (U : X.affineOpens) ↦
        letI : IsAffine (U : X.Opens).toScheme := U.property
        Spec.map (algebra a b (U : X.Opens)).hom ≫ (U : X.Opens).toScheme.isoSpec.inv
      naturality := sorry }
  equifibered := fun {U V : X.affineOpens} h ↦ chartPullback a b (leOfHom h)

/-- The actual affine-glued coequalizer scheme. -/
abbrev scheme : Scheme.{u} := (gluingData a b).glued

/-- Its actual structural morphism, descended from the affine structure maps. -/
def toBase : scheme a b ⟶ X := (gluingData a b).toBase

/-- The affine inverse-image chart identification from actual native open gluing. -/
def localIso (U : X.affineOpens) :
    ((toBase a b) ⁻¹ᵁ (U : X.Opens)).toScheme ≅ Spec (ring a b U) :=
  (scheme a b).isoOfEq
      (by
        have h := (gluingData a b).toBase_preimage_eq_opensRange_ι U
        change (toBase a b) ⁻¹ᵁ (U : X.Opens).ι.opensRange = _ at h
        rw [Scheme.Opens.opensRange_ι] at h
        exact h) ≪≫
    (colimit.ι (gluingData a b).functor U).isoOpensRange.symm

/-- The quotient's affine inverses are supplied by the native glued chart isomorphisms. -/
theorem isAffineHom : IsAffineHom (toBase a b) where
  isAffine_preimage U hU :=
    letI := (localIso a b ⟨U, hU⟩).isIso_hom
    IsAffine.of_isIso (localIso a b ⟨U, hU⟩).hom

/-- The section equalizer is finite, by the étale-local split finite-product computation. -/
theorem finite_app (U : X.Opens) (hU : IsAffineOpen U) :
    ((toBase a b).app U).hom.Finite := sorry

/-- Finiteness stores the already constructed affine inverse data. -/
theorem isFinite : IsFinite (toBase a b) where
  toIsAffineHom := isAffineHom a b
  finite_app := finite_app a b

/-- The section equalizer is étale, by the same source-local split-product computation. -/
theorem etale : Etale (toBase a b) := sorry

/-- The actual finite étale coequalizer object. -/
def obj : FiniteEtale X :=
  MorphismProperty.Over.mk _ (toBase a b) ⟨isFinite a b, etale a b⟩

/-- The quotient map on the pullback of one affine base chart. -/
def quotientChart (U : X.affineOpens) :
    pullback Y.hom (U : X.Opens).ι ⟶ scheme a b :=
  (pullbackRestrictIsoRestrict Y.hom (U : X.Opens)).hom ≫
    (preimage Y U).toScheme.toSpecΓ ≫
      Spec.map (inclusion a b U) ≫ colimit.ι (gluingData a b).functor U

/-- Glue the literal equalizer-inclusion maps to the quotient scheme map. -/
def quotient : Y.left ⟶ scheme a b :=
  Scheme.Cover.glueMorphisms (X.directedAffineCover.pullback₁ Y.hom)
    (fun (U : X.affineOpens) ↦ quotientChart a b U) sorry

/-- The actual quotient morphism in the finite étale category. -/
def π : Y ⟶ obj a b :=
  MorphismProperty.Over.homMk (quotient a b) sorry

/-- Equalizing maps give section maps into the literal subring by codomain restriction. -/
theorem descRingHom_mem {W : FiniteEtale X} (h : Y ⟶ W) (hab : a ≫ h = b ≫ h)
    (U : X.Opens) (s : sectionRing W U) :
    (sectionMap a U).right ((sectionMap h U).right s) =
      (sectionMap b U).right ((sectionMap h U).right s) := sorry

/-- Factor the actual section map through the equalizer using the supplied equality. -/
def descRingHom {W : FiniteEtale X} (h : Y ⟶ W) (hab : a ≫ h = b ≫ h)
    (U : X.Opens) : sectionRing W U ⟶ ring a b U :=
  CommRingCat.ofHom
    { toFun := fun s ↦ ⟨(sectionMap h U).right s, descRingHom_mem a b h hab U s⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Descend on each affine chart using the native affine inverse of the given target. -/
def descChart {W : FiniteEtale X} (h : Y ⟶ W) (hab : a ≫ h = b ≫ h)
    (U : X.affineOpens) : Spec (ring a b U) ⟶ W.left :=
  Spec.map (descRingHom a b h hab U) ≫
    (preimage W U).toScheme.isoSpec.inv ≫ (preimage W U).ι

/-- Compatible affine universal maps form the actual descent cocone. -/
def descCocone {W : FiniteEtale X} (h : Y ⟶ W) (hab : a ≫ h = b ≫ h) :
    Cocone (gluingData a b).functor where
  pt := W.left
  ι := { app := fun (U : X.affineOpens) ↦ descChart a b h hab U, naturality := sorry }

/-- The universal coequalizer map is the actual scheme colimit descent. -/
def desc {W : FiniteEtale X} (h : Y ⟶ W) (hab : a ≫ h = b ≫ h) : obj a b ⟶ W :=
  MorphismProperty.Over.homMk (colimit.desc _ (descCocone a b h hab)) sorry

/-- The quotient leg equalizes the original two arrows. -/
theorem condition : a ≫ π a b = b ≫ π a b := sorry

/-- The cofork retains the literal equalizer quotient object and leg. -/
def cofork : Cofork a b := Cofork.ofπ (π a b) (condition a b)

/-- The universal desc is the actual affine section factorization. -/
def isColimit : IsColimit (cofork a b) :=
  Cofork.IsColimit.mk _ (fun c ↦ desc a b c.π c.condition) sorry sorry

/-- On each quotient chart the universal map is the explicit contravariant ring map. -/
theorem ι_desc {W : FiniteEtale X} (h : Y ⟶ W) (hab : a ≫ h = b ≫ h)
    (U : X.affineOpens) :
    colimit.ι (gluingData a b).functor U ≫ (desc a b h hab).left =
      descChart a b h hab U := sorry

end Coequalizer

/-- Finite étale coequalizers have actual affine-glued objects and desc maps. -/
instance hasCoequalizer {Z Y : FiniteEtale X} (a b : Z ⟶ Y) : HasCoequalizer a b :=
  ⟨⟨_, Coequalizer.isColimit a b⟩⟩

/-- The parallel-pair instances retain the explicit coequalizer cocones. -/
instance hasCoequalizers : HasCoequalizers (FiniteEtale X) :=
  hasCoequalizers_of_hasColimit_parallelPair (FiniteEtale X)

namespace FiniteGroupQuotient

variable {G : Type u} [Group G] [Finite G] (F : SingleObj G ⥤ FiniteEtale X)

/-- The underlying finite étale scheme of the action. -/
abbrev object : FiniteEtale X := F.obj (SingleObj.star G)

/-- One copy of the acted-on scheme for every group element. -/
def relations : FiniteEtale X := coproduct (fun _ : G ↦ object F)

/-- The action map from the actual finite disjoint union. -/
def action : relations F ⟶ object F :=
  coproductDesc (fun _ : G ↦ object F) (fun g ↦ F.map g)

/-- The projection map from the same finite disjoint union. -/
def projection : relations F ⟶ object F :=
  coproductDesc (fun _ : G ↦ object F) (fun _ ↦ 𝟙 (object F))

/-- The actual quotient cocone has the section-equalizer coequalizer as its vertex. -/
def cocone : Cocone F where
  pt := Coequalizer.obj (action F) (projection F)
  ι :=
    { app := fun j ↦ by
        cases j
        exact Coequalizer.π (action F) (projection F)
      naturality := sorry }

/-- The supplied action cocone gives the precise equalizing condition for descent. -/
theorem descCondition (c : Cocone F) :
    action F ≫ c.ι.app (SingleObj.star G) =
      projection F ≫ c.ι.app (SingleObj.star G) := sorry

/-- Descend an invariant map through the actual section-equalizer quotient. -/
def isColimit : IsColimit (cocone F) where
  desc c := Coequalizer.desc (action F) (projection F)
    (c.ι.app (SingleObj.star G)) (descCondition F c)
  fac := sorry
  uniq := sorry

end FiniteGroupQuotient

/-- Actual finite-group quotient cocones use the group-action coproduct and coequalizer. -/
def finiteGroupQuotientCocone {G : Type u} [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtale X) : ColimitCocone F :=
  ⟨FiniteGroupQuotient.cocone F, FiniteGroupQuotient.isColimit F⟩

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme

/-- Finite colimits are constructed from the actual disjoint unions and section equalizers. -/
instance finiteEtale_hasFiniteColimits (X : Scheme.{u}) :
    HasFiniteColimits (FiniteEtale X) :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end AlgebraicGeometry.Scheme
