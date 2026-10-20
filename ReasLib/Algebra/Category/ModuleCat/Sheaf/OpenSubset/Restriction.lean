module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenSubset
public import ReasLib.Algebra.Category.Ring.Sheaf.OpenSubset

/-!
# Restriction of module sheaves between open subspaces

This module owns restriction between nested open subspaces, its coherent composition maps, the
open-immersion presentation, and the comparison after forgetting to additive sheaves.  It is
independent of any chosen covering family.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens
open TopCat.Opens.Subspace

noncomputable section

universe w u

section

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

open scoped TopCat
open TopCat.Sheaf.OpenSubset TopCat.Sheaf.OpenSubset.Restriction

namespace SheafOfModules.OpenSubset.Restriction

/-- Restriction of module sheaves along an inclusion `W ≤ U` of open subsets. -/
noncomputable abbrev restrict
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    SheafOfModules.{w} (𝒪 |_ U) ⥤
      SheafOfModules.{w} (𝒪 |_ W) :=
  SheafOfModules.pullback.{w} (toPushforward 𝒪 h)

/-- Restriction of `(𝒪 |_ U)`-modules to `(𝒪 |_ (U ⊓ V))`-modules along
`inf_le_left : U ⊓ V ≤ U`. -/
noncomputable abbrev toPairLeft
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V)) :=
  restrict 𝒪 inf_le_left

/-- Restriction of `(𝒪 |_ V)`-modules to `(𝒪 |_ (U ⊓ V))`-modules along
`inf_le_right : U ⊓ V ≤ V`. -/
noncomputable abbrev toPairRight
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    SheafOfModules (𝒪 |_ V) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V)) :=
  restrict 𝒪 inf_le_right

/-- Restriction from the first member `U` to the triple overlap `U ⊓ V ⊓ W`. -/
abbrev toTripleFirst
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  restrict 𝒪 (inf_le_left.trans inf_le_left)

/-- Restriction from the second member `V` to the triple overlap `U ⊓ V ⊓ W`. -/
abbrev toTripleSecond
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ V) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  restrict 𝒪 (inf_le_left.trans inf_le_right)

/-- Restriction from the third member `W` to the triple overlap `U ⊓ V ⊓ W`. -/
abbrev toTripleThird
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ W) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  restrict 𝒪 inf_le_right

/-- Restriction from the overlap `U ⊓ V` to `U ⊓ V ⊓ W`. -/
abbrev overlapToTripleLeft
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (U ⊓ V)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  restrict 𝒪 inf_le_left

/-- Restriction from the overlap `V ⊓ W` to `U ⊓ V ⊓ W`. -/
abbrev overlapToTripleCenter
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (V ⊓ W)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  restrict 𝒪 (inf_le_inf inf_le_right le_rfl)

/-- Restriction from the overlap `U ⊓ W` to `U ⊓ V ⊓ W`. -/
abbrev overlapToTripleOuter
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (U ⊓ W)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  restrict 𝒪 (inf_le_inf inf_le_left le_rfl)

/-- Successive restriction along `T ≤ W ≤ U` agrees with direct restriction from `U` to `T`. -/
noncomputable def compIso
    (𝒪 : TopCat.Sheaf RingCat X) {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    restrict 𝒪 hWU ⋙ restrict 𝒪 hTW ≅
      restrict 𝒪 (hTW.trans hWU) :=
  (SheafOfModules.pullbackComp
      (toPushforward 𝒪 hWU)
      (toPushforward 𝒪 hTW)) ≪≫
    eqToIso (congrArg (fun φ ↦ SheafOfModules.pullback φ)
      (toPushforward_comp 𝒪 hTW hWU))

/-- Restriction from `X` to `U` and then to `W ≤ U` agrees with direct restriction to `W`. -/
noncomputable def ambientCompIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    functor U 𝒪 ⋙ restrict 𝒪 h ≅
      functor W 𝒪 :=
  (SheafOfModules.pullbackComp
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (inclusion U)).unit.app 𝒪)
      (toPushforward 𝒪 h)) ≪≫
    eqToIso (congrArg (fun φ ↦ SheafOfModules.pullback φ)
      (toPushforward_comp_inclusion 𝒪 h))

/-- Comparison between direct restriction from `U` to the triple overlap and restriction through
`U ⊓ V`. -/
noncomputable def firstViaLeftIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    toTripleFirst 𝒪 U V W ≅
      toPairLeft 𝒪 U V ⋙ overlapToTripleLeft 𝒪 U V W :=
  (compIso 𝒪 inf_le_left inf_le_left).symm

/-- Comparison between direct restriction from `V` to the triple overlap and restriction through
`U ⊓ V`. -/
noncomputable def secondViaLeftIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    toTripleSecond 𝒪 U V W ≅
      toPairRight 𝒪 U V ⋙ overlapToTripleLeft 𝒪 U V W :=
  (compIso 𝒪 inf_le_left inf_le_right).symm

/-- Comparison between direct restriction from `V` to the triple overlap and restriction through
`V ⊓ W`. -/
noncomputable def secondViaCenterIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    toTripleSecond 𝒪 U V W ≅
      toPairLeft 𝒪 V W ⋙ overlapToTripleCenter 𝒪 U V W :=
  (compIso 𝒪
    (inf_le_inf inf_le_right le_rfl) inf_le_left).symm

/-- Comparison between direct restriction from `W` to the triple overlap and restriction through
`V ⊓ W`. -/
noncomputable def thirdViaCenterIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    toTripleThird 𝒪 U V W ≅
      toPairRight 𝒪 V W ⋙ overlapToTripleCenter 𝒪 U V W :=
  (compIso 𝒪
    (inf_le_inf inf_le_right le_rfl) inf_le_right).symm

/-- Comparison between direct restriction from `U` to the triple overlap and restriction through
`U ⊓ W`. -/
noncomputable def firstViaOuterIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    toTripleFirst 𝒪 U V W ≅
      toPairLeft 𝒪 U W ⋙ overlapToTripleOuter 𝒪 U V W :=
  (compIso 𝒪
    (inf_le_inf inf_le_left le_rfl) inf_le_left).symm

/-- Comparison between direct restriction from `W` to the triple overlap and restriction through
`U ⊓ W`. -/
noncomputable def thirdViaOuterIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    toTripleThird 𝒪 U V W ≅
      toPairRight 𝒪 U W ⋙ overlapToTripleOuter 𝒪 U V W :=
  (compIso 𝒪
    (inf_le_inf inf_le_left le_rfl) inf_le_right).symm

/-- Direct restriction from `X` to `U ⊓ V` agrees with restriction through `U`. -/
noncomputable def toPairViaLeftIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    functor (U ⊓ V) 𝒪 ≅
      functor U 𝒪 ⋙ toPairLeft 𝒪 U V :=
  (ambientCompIso 𝒪 inf_le_left).symm

/-- Direct restriction from `X` to `U ⊓ V` agrees with restriction through `V`. -/
noncomputable def toPairViaRightIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    functor (U ⊓ V) 𝒪 ≅
      functor V 𝒪 ⋙ toPairRight 𝒪 U V :=
  (ambientCompIso 𝒪 inf_le_right).symm

/-- Scalar comparison identifying restriction to `W` with pullback along the open immersion
`W ↪ U`. -/
noncomputable def openEmbeddingScalarIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (𝒪 |_ W) ≅
      ((TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).sheafPullback RingCat).obj (𝒪 |_ U) :=
  (TopCat.Sheaf.OpenSubset.Restriction.pullbackIso 𝒪 h).symm ≪≫
    ((TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).sheafPullbackIso RingCat).app (𝒪 |_ U)

/-- The open-embedding model of restriction from `U` to `W`, with scalars transported through
`openEmbeddingScalarIso`. -/
noncomputable def openEmbeddingRestrict
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    SheafOfModules (𝒪 |_ U) ⥤ SheafOfModules (𝒪 |_ W) :=
  SheafOfModules.pushforward.{w}
    (F := (TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).functor)
    (openEmbeddingScalarIso 𝒪 h).hom

/-- The scalar comparison for open-immersion pushforward is compatible with the counit of the
adjunction on opens. -/
theorem openEmbeddingScalarIso_counit
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    Functor.whiskerRight
        (NatTrans.op (TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).isOpenMap.adjunction.counit)
        (𝒪 |_ U).obj =
      (toPushforward 𝒪 h).hom ≫
        (restrictionFunctor h).op.whiskerLeft
          (openEmbeddingScalarIso 𝒪 h).hom.hom := sorry

/-- The scalar comparison for open-immersion pushforward is compatible with the unit of the
adjunction on opens. -/
theorem openEmbeddingScalarIso_unit
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (openEmbeddingScalarIso 𝒪 h).hom.hom ≫
        (TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).functor.op.whiskerLeft
          (toPushforward 𝒪 h).hom ≫
        Functor.whiskerRight
          (NatTrans.op (TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).isOpenMap.adjunction.unit)
          (𝒪 |_ W).obj =
      𝟙 (𝒪 |_ W).obj := sorry

/-- The module pushforward along the open immersion `W ↪ U` is left adjoint to internal
restriction from `U` to `W`. -/
noncomputable def openEmbeddingRestrictAdjunction
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    openEmbeddingRestrict 𝒪 h ⊣
      SheafOfModules.pushforward.{w} (toPushforward 𝒪 h) :=
  SheafOfModules.pushforwardPushforwardAdj
    (adj := (TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).isOpenMap.adjunction)
    (openEmbeddingScalarIso 𝒪 h).hom
    (toPushforward 𝒪 h)
    (openEmbeddingScalarIso_counit 𝒪 h)
    (openEmbeddingScalarIso_unit 𝒪 h)

/-- The open-immersion model and the pullback model of module restriction are canonically
isomorphic. -/
noncomputable def openEmbeddingRestrictIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    openEmbeddingRestrict 𝒪 h ≅ restrict 𝒪 h :=
  Adjunction.leftAdjointUniq
    (openEmbeddingRestrictAdjunction 𝒪 h)
    (SheafOfModules.pullbackPushforwardAdjunction (toPushforward 𝒪 h))

/-- After forgetting module structures, open-immersion pushforward agrees with pullback of
`AddCommGrpCat`-valued sheaves. -/
theorem toAddCommGrp_openEmbeddingRestrict_eq
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    SheafOfModules.toSheaf (𝒪 |_ U) ⋙
        (TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w} =
      openEmbeddingRestrict 𝒪 h ⋙ SheafOfModules.toSheaf (𝒪 |_ W) := sorry

/-- Forgetting module structure commutes, up to canonical natural isomorphism, with restriction
along an inclusion `W ≤ U` of open subsets. -/
noncomputable def toAddCommGrpNatIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    SheafOfModules.toSheaf (𝒪 |_ U) ⋙
        (TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w} ≅
      restrict 𝒪 h ⋙ SheafOfModules.toSheaf (𝒪 |_ W) :=
  eqToIso (toAddCommGrp_openEmbeddingRestrict_eq 𝒪 h) ≪≫
    Functor.isoWhiskerRight (openEmbeddingRestrictIso 𝒪 h)
      (SheafOfModules.toSheaf (𝒪 |_ W))

/-- Objectwise form of `toAddCommGrpNatIso`. -/
noncomputable abbrev toAddCommGrpIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    ((TopCat.Opens.Subspace.homOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ W)).obj
        ((restrict 𝒪 h).obj ℱ) :=
  (toAddCommGrpNatIso 𝒪 h).app ℱ

/-- The additive-sheaf comparison for restricting a module sheaf from `U` to `U ⊓ V`. -/
noncomputable abbrev toAddCommGrpToPairLeftIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) (ℱ : SheafOfModules (𝒪 |_ U)) :=
  toAddCommGrpIso 𝒪 (W := U ⊓ V) (U := U) inf_le_left ℱ

/-- The additive-sheaf comparison for restricting a module sheaf from `V` to `U ⊓ V`. -/
noncomputable abbrev toAddCommGrpToPairRightIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) (ℱ : SheafOfModules (𝒪 |_ V)) :=
  toAddCommGrpIso 𝒪 (W := U ⊓ V) (U := V) inf_le_right ℱ

/-- The section map underlying the forward additive-sheaf restriction comparison. -/
abbrev toAddCommGrpHomApp
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U)
    (ℱ : SheafOfModules (𝒪 |_ U)) (V : (Opens (space W))ᵒᵖ) :
    ((openEmbeddingRestrict 𝒪 h).obj ℱ).val.obj V →
      ((restrict 𝒪 h).obj ℱ).val.obj V :=
  fun m ↦ ((toAddCommGrpIso 𝒪 h ℱ).hom.hom.app V).hom m

/-- The section map underlying the inverse additive-sheaf restriction comparison. -/
abbrev toAddCommGrpInvApp
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U)
    (ℱ : SheafOfModules (𝒪 |_ U)) (V : (Opens (space W))ᵒᵖ) :
    ((restrict 𝒪 h).obj ℱ).val.obj V →
      ((openEmbeddingRestrict 𝒪 h).obj ℱ).val.obj V :=
  fun m ↦ ((toAddCommGrpIso 𝒪 h ℱ).inv.hom.app V).hom m

end SheafOfModules.OpenSubset.Restriction
