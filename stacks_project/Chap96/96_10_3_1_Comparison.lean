module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import stacks_project.Chap65.Lemma_65_7_2_Pullback
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap96.Lemma_96_10_1_Comparison
public import stacks_project.Chap96.«96_10_3_1_Restriction»

/-!
# Big-versus-small étale pushforward comparison

For a morphism `f : F ⟶ G` of algebraic spaces, the restriction of the CFG
pushforward `f_* ℱ` to `G_étale` is canonically identified with the small étale
pushforward of the restriction of `ℱ` to `F_étale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite FiberedCategoryOver.Groupoids
open CategoryTheory.CategoryOfElements
open CategoryTheory.Sheaf.InternalModule
open Limits.Types
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The CFG étale pushforward `f_*` associated to a morphism of algebraic spaces,
as the direct image of the morphism of topoi induced by `toGroupoids.map f`. -/
abbrev etalePushforward {F G : AlgebraicSpace S} (f : F ⟶ G)
    [HasSheafify F.toGroupoids.etaleTopology (Type (u + 1))]
    [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.HasPointwiseRightKanExtension P] :
    Sheaf F.toGroupoids.etaleTopology (Type (u + 1)) ⥤
      Sheaf G.toGroupoids.etaleTopology (Type (u + 1)) :=
  (toCartesianBasedFunctor (toGroupoids.map f)).morphismOfTopoiIn
    (StandardTopology.etale.overTopology S) |>.pushforward

/-- The comma category computing `f_* ℱ` at the tautological object `u_G(V)`. -/
abbrev compareBigIndex {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :=
  StructuredArrow (op ((smallEtaleToGroupoids G).obj V))
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op

/-- The comma category computing `f_small,* (ℱ |_{F_étale})` at `V ×_G F`. -/
abbrev compareSmallIndex {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :=
  StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion F).op

/-- The Kan-extension diagram for the CFG pushforward at `u_G(V)`. -/
abbrev compareBigDiag {F G : AlgebraicSpace S} (f : F ⟶ G)
    (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1))) (V : smallEtaleSite G) :
    compareBigIndex f V ⥤ Type (u + 1) :=
  StructuredArrow.proj (op ((smallEtaleToGroupoids G).obj V))
      (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op ⋙
    ℱ.obj

/-- The Kan-extension diagram for the small étale pushforward at `V ×_G F`. -/
abbrev compareSmallDiag {F G : AlgebraicSpace S} (f : F ⟶ G)
    (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1))) (V : smallEtaleSite G) :
    compareSmallIndex f V ⥤ Type (u + 1) :=
  StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion F).op ⋙
    ((restrictEtale F).obj ℱ).obj

/-- The underlying scheme over `S` of a comma object computing `f_* ℱ` at `u_G(V)`. -/
def compareBigScheme {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (k : compareSmallIndex f V) : Over S :=
  k.right.unop.left

/-- The morphism `ofOver U ⟶ V ×_G F` underlying a comma object of the small
étale pushforward diagram. -/
def compareSmallToBaseChange {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (k : compareSmallIndex f V) :
    ofOver (compareBigScheme f k) ⟶ etaleBaseChangeSpace f V :=
  k.hom.unop.left

/-- The morphism in `Over S` from the domain of a small-étale comma object to `V`,
obtained by Yoneda from the projection `U ⟶ V ×_G F ⟶ V`. -/
def compareOverHom {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (k : compareSmallIndex f V) : compareBigScheme f k ⟶ V.left :=
  yonedaEquiv (compareSmallToBaseChange f k ≫ etaleBaseChangeSnd f V)

/-- The morphism `f(u_F(U)) ⟶ u_G(V)` in `G.toGroupoids` induced by a scheme
étale over `F` lying over `V ×_G F`. -/
def compareIndexHom {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (k : compareSmallIndex f V) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.obj
        ((smallEtaleToGroupoids F).obj k.right.unop) ⟶
      (smallEtaleToGroupoids G).obj V :=
  (homMk
      (unop ((smallEtaleToGroupoids G).obj V))
      (unop ((toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.obj
          ((smallEtaleToGroupoids F).obj k.right.unop)))
      (compareOverHom f k).op sorry).op

/-- The morphism in `G.totalᵒᵖ` presenting a small-étale comma object as a
comma object for the CFG pushforward. -/
def compareIndexArrow {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (k : compareSmallIndex f V) :
    op ((smallEtaleToGroupoids G).obj V) ⟶
      (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.obj
        (op ((smallEtaleToGroupoids F).obj k.right.unop)) :=
  (compareIndexHom f k).op

/-- The functor from the small-étale Kan comma category to the CFG Kan comma
category, sending `U → V ×_G F` to the tautological object `u_F(U)`. -/
def compareIndexMap {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :
    compareSmallIndex f V ⥤ compareBigIndex f V where
  obj k := StructuredArrow.mk (compareIndexArrow f k)
  map {k k'} α :=
    StructuredArrow.homMk ((smallEtaleToGroupoids F).map α.right.unop).op sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The Kan-extension diagrams are identified after restriction along `compareIndexMap`,
because sections of `ℱ |_{F_étale}` at `U` are sections of `ℱ` at `u_F(U)`. -/
def compareDiagIso {F G : AlgebraicSpace S} (f : F ⟶ G)
    (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1))) (V : smallEtaleSite G) :
    compareIndexMap f V ⋙ compareBigDiag f ℱ V ≅ compareSmallDiag f ℱ V :=
  NatIso.ofComponents (fun k => Iso.refl _) sorry

/-- An étale atlas scheme of `F`, extracted from the atlas field. -/
def compareAtlasScheme (F : AlgebraicSpace S) : Over S :=
  Classical.choose F.atlas

/-- The atlas morphism `ofOver (compareAtlasScheme F) ⟶ F`. -/
def compareAtlasHom (F : AlgebraicSpace S) : ofOver (compareAtlasScheme F) ⟶ F :=
  Exists.choose (Classical.choose_spec F.atlas)

/-- The chosen atlas section of `F.atlas` is étale as a morphism of functors of
points, and étale-locally surjective. -/
theorem compareAtlasHom_spec (F : AlgebraicSpace S) :
    MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) (compareAtlasHom F) ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (compareAtlasHom F) :=
  sorry

/-- The chosen atlas morphism is étale as a morphism of algebraic spaces. -/
instance compareAtlasHom_isEtale (F : AlgebraicSpace S) : Etale (compareAtlasHom F) :=
  sorry

/-- The scheme `U₀ = atlas_F ×_G V` covering `V ×_G F`. -/
def coverScheme {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) : Over S :=
  pullbackOverAtlas (homFunctor f) V.hom G.representableDiagonal
    (compareAtlasHom F) (𝟙 _)

/-- The structure morphism `U₀ ⟶ F`. -/
def coverHom {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :
    ofOver (coverScheme f V) ⟶ F :=
  pullbackOverAtlasFst (homFunctor f) V.hom G.representableDiagonal
      (compareAtlasHom F) (𝟙 _) ≫
    compareAtlasHom F

/-- The covering morphism `U₀ ⟶ F` is étale, as the composite of a pullback of
the chosen étale atlas `compareAtlasHom F` with that atlas morphism. -/
instance coverHom_isEtale {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :
    Etale (coverHom f V) :=
  sorry

/-- The object of `F_étale` classified by the covering morphism `U₀ ⟶ F`. -/
def coverSite {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :
    smallEtaleSite F :=
  smallEtaleSite.mk (coverHom f V)

/-- The morphism `U₀ ⟶ V ×_G F` of algebraic spaces. -/
def coverToBaseChange {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :
    ofOver (coverScheme f V) ⟶ etaleBaseChangeSpace f V :=
  pullbackOverAtlasHom (homFunctor f) V.hom G.representableDiagonal
    (compareAtlasHom F) (𝟙 _)

/-- The covering object as a morphism of the spaces étale site of `F`. -/
def coverOverHom {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :
    (smallEtaleInclusion F).obj (coverSite f V) ⟶ (etaleBaseChange f).obj V :=
  MorphismProperty.Over.homMk (coverToBaseChange f V) sorry

/-- The covering object as a comma object of the small étale pushforward diagram. -/
def coverIndex {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :
    compareSmallIndex f V :=
  StructuredArrow.mk (op (coverOverHom f V))

/-- The underlying scheme of a CFG comma object computing `f_* ℱ` at `u_G(V)`. -/
def compareBigDomain {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) : Over S :=
  (unop (j.right.unop)).1.unop

/-- The Yoneda section of a CFG comma object. -/
def compareBigSection {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    F.functorOfPoints.obj (op (compareBigDomain f j)) :=
  (unop (j.right.unop)).2

/-- The morphism `T ⟶ F` classified by a CFG comma object. -/
def compareBigToF {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    ofOver (compareBigDomain f j) ⟶ F :=
  yonedaEquiv.symm (compareBigSection f j)

/-- The scheme `T ×_F U₀` obtained by pulling the atlas cover back along `T ⟶ F`. -/
def compareFibreScheme {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) : Over S :=
  pullbackOverAtlas (compareBigToF f j) (coverHom f V) F.representableDiagonal
    (𝟙 _) (𝟙 _)

/-- The projection `T ×_F U₀ ⟶ T`. -/
def compareFibreToDomain {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    yoneda.obj (compareFibreScheme f j) ⟶ yoneda.obj (compareBigDomain f j) :=
  pullbackOverAtlasFst (compareBigToF f j) (coverHom f V) F.representableDiagonal
    (𝟙 _) (𝟙 _)

/-- The projection `T ×_F U₀ ⟶ U₀`. -/
def compareFibreToCoverScheme {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    compareFibreScheme f j ⟶ coverScheme f V :=
  pullbackOverAtlasSnd (compareBigToF f j) (coverHom f V) F.representableDiagonal
    (𝟙 _) (𝟙 _)

/-- The morphism `T ×_F U₀ ⟶ F`. -/
def compareFibreHom {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    ofOver (compareFibreScheme f j) ⟶ F :=
  yoneda.map (compareFibreToCoverScheme f j) ≫ coverHom f V

/-- The object of `S_F` classified by `T ×_F U₀ ⟶ F`. -/
def compareFibreObj {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) : F.toGroupoids.total :=
  op ⟨op (compareFibreScheme f j),
    yonedaEquiv (compareFibreHom f j)⟩

/-- The morphism `T ×_F U₀ ⟶ U₀` in `S_F`. -/
def compareFibreToCover {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    compareFibreObj f j ⟶ (smallEtaleToGroupoids F).obj (coverSite f V) :=
  (homMk
      (unop ((smallEtaleToGroupoids F).obj (coverSite f V)))
      (unop (compareFibreObj f j))
      (compareFibreToCoverScheme f j).op sorry).op

/-- The morphism `T ×_F U₀ ⟶ T` in `S_F`. -/
def compareFibreToBig {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    compareFibreObj f j ⟶ j.right.unop :=
  (homMk
      (unop (j.right.unop))
      (unop (compareFibreObj f j))
      (yonedaEquiv (compareFibreToDomain f j)).op sorry).op

/-- The covering family `{T ×_F U₀ ⟶ T}` is an étale covering in `S_F`. -/
theorem compareFibre_cover_mem {F G : AlgebraicSpace S} (f : F ⟶ G)
    {V : smallEtaleSite G} (j : compareBigIndex f V) :
    Sieve.ofArrows (fun _ : Unit => compareFibreObj f j)
        (fun _ => compareFibreToBig f j) ∈
      F.toGroupoids.etaleTopology (j.right.unop) :=
  sorry

section CompareTypeSucc

variable {F G : AlgebraicSpace S} (f : F ⟶ G)
variable (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1)))
variable [HasSheafify F.toGroupoids.etaleTopology (Type (u + 1))]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.HasPointwiseRightKanExtension P]

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category. -/
def compareLimitHom (V : smallEtaleSite G) :
    limit (compareBigDiag f ℱ V) ⟶ limit (compareSmallDiag f ℱ V) :=
  limit.pre (compareBigDiag f ℱ V) (compareIndexMap f V) ≫
    (HasLimit.isoOfNatIso (compareDiagIso f ℱ V)).hom

/-- Restriction of a small-étale compatible family to the atlas cover `U₀`. -/
def compareCoverSection (V : smallEtaleSite G) :
    limit (compareSmallDiag f ℱ V) ⟶
      ℱ.obj.obj (op ((smallEtaleToGroupoids F).obj (coverSite f V))) :=
  (HasLimit.isoOfNatIso (compareDiagIso f ℱ V)).inv ≫
    limit.π (compareIndexMap f V ⋙ compareBigDiag f ℱ V) (coverIndex f V)

/-- The family of sections of `ℱ` on `T ×_F U₀` obtained by restricting the atlas
cover section. -/
def compareFibreSection (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiag f ℱ V) ⟶ ℱ.obj.obj (op (compareFibreObj f j)) :=
  compareCoverSection f ℱ V ≫ ℱ.obj.map (compareFibreToCover f j).op

/-- Compatibility of the one-arrow covering family on `T ×_F U₀`. -/
theorem compareFibreSection_compatible (V : smallEtaleSite G)
    (j : compareBigIndex f V) :
    ∀ ⦃W : F.toGroupoids.total⦄ ⦃i k : Unit⦄
      (a : W ⟶ compareFibreObj f j) (b : W ⟶ compareFibreObj f j),
      a ≫ compareFibreToBig f j = b ≫ compareFibreToBig f j →
        compareFibreSection f ℱ V j ≫ ℱ.obj.map a.op =
          compareFibreSection f ℱ V j ≫ ℱ.obj.map b.op :=
  sorry

/-- Component of the reverse comparison cone at a CFG comma object. -/
def compareInvπ (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiag f ℱ V) ⟶ (compareBigDiag f ℱ V).obj j :=
  ℱ.property.amalgamateOfArrows
    (fun _ : Unit => compareFibreToBig f j)
    (compareFibre_cover_mem f j)
    (fun _ => compareFibreSection f ℱ V j)
    (compareFibreSection_compatible f ℱ V j)

/-- Extension of a small-étale compatible family to a CFG compatible family, by
amalgamating along the étale cover `T ×_F U₀ ⟶ T`. -/
def compareLimitInv (V : smallEtaleSite G) :
    limit (compareSmallDiag f ℱ V) ⟶ limit (compareBigDiag f ℱ V) :=
  limit.lift (compareBigDiag f ℱ V)
    { pt := limit (compareSmallDiag f ℱ V)
      π :=
        { app := compareInvπ f ℱ V
          naturality := sorry } }

/-- Canonical identification of the two Kan-extension limits at `V`. -/
def compareLimitIso (V : smallEtaleSite G) :
    limit (compareBigDiag f ℱ V) ≅ limit (compareSmallDiag f ℱ V) where
  hom := compareLimitHom f ℱ V
  inv := compareLimitInv f ℱ V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The spaces-étale extension of `ℱ |_{F_étale}` used by `f_small,*`. -/
abbrev compareSmallExtended :
    Sheaf (spacesEtaleTopology F) (Type (u + 1)) :=
  ((smallEtaleInclusion F).sheafPushforwardCocontinuous (Type (u + 1))
      (smallEtaleTopology F) (spacesEtaleTopology F)).obj
    ((restrictEtale F).obj ℱ)

/-- Sectionwise identification of `(f_* ℱ)(u_G(V))` with
`f_small,* (ℱ |_{F_étale})(V)`. -/
def compareBigSmall_app (V : smallEtaleSite G) :
    ((restrictEtale G).obj ((etalePushforward f).obj ℱ)).obj.obj (op V) ≅
      ((sheafPushforwardType f).obj ((restrictEtale F).obj ℱ)).obj.obj (op V) :=
  (sheafPushforwardContinuousObjObjIso (smallEtaleToGroupoids G) (Type (u + 1))
      ((etalePushforward f).obj ℱ) V) ≪≫
    ((toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.ranObjObjIsoLimit
        ℱ.obj (op ((smallEtaleToGroupoids G).obj V))) ≪≫
      compareLimitIso f ℱ V ≪≫
        ((smallEtaleInclusion F).op.ranObjObjIsoLimit
            ((restrictEtale F).obj ℱ).obj
            (op ((etaleBaseChange f).obj V))).symm ≪≫
          (sheafPushforwardContinuousObjObjIso (etaleBaseChange f) (Type (u + 1))
              (compareSmallExtended ℱ) V).symm

/-- Underlying presheaf identification of the two composites. -/
def compareBigSmallPresheaf :
    ((restrictEtale G).obj ((etalePushforward f).obj ℱ)).obj ≅
      ((sheafPushforwardType f).obj ((restrictEtale F).obj ℱ)).obj :=
  NatIso.ofComponents (fun V => compareBigSmall_app f ℱ V.unop) sorry

/-- The canonical identification
`(f_* ℱ)|_{G_étale} = f_small,* (ℱ |_{F_étale})` of sheaves on `G_étale`. -/
def compareBigSmall :
    (restrictEtale G).obj ((etalePushforward f).obj ℱ) ≅
      (sheafPushforwardType f).obj ((restrictEtale F).obj ℱ) where
  hom := CategoryTheory.ObjectProperty.homMk (compareBigSmallPresheaf f ℱ).hom
  inv := CategoryTheory.ObjectProperty.homMk (compareBigSmallPresheaf f ℱ).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `compareBigSmall` is the sectionwise identification `compareBigSmall_app`. -/
theorem compareBigSmall_app_eq (V : smallEtaleSite G) :
    ((sheafToPresheaf (smallEtaleTopology G) (Type (u + 1))).mapIso
          (compareBigSmall f ℱ)).app (op V) =
      compareBigSmall_app f ℱ V :=
  sorry

/-- The identification is natural in the étale sheaf `ℱ`. -/
theorem compareBigSmall_natural
    {ℱ 𝒢 : Sheaf F.toGroupoids.etaleTopology (Type (u + 1))} (τ : ℱ ⟶ 𝒢) :
    (restrictEtale G).map ((etalePushforward f).map τ) ≫ (compareBigSmall f 𝒢).hom =
      (compareBigSmall f ℱ).hom ≫
        (sheafPushforwardType f).map ((restrictEtale F).map τ) :=
  sorry

end CompareTypeSucc

/-- Ring-valued sheaves on an associated étale topology compose with `forget RingCat`. -/
instance toGroupoids_etale_hasSheafCompose_ring (X : GroupoidsOver S) :
    X.etaleTopology.HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Type-valued sheafification exists on an associated étale topology in universe `u`. -/
instance toGroupoids_etale_hasSheafify_type (X : GroupoidsOver S) :
    HasSheafify X.etaleTopology (Type u) :=
  sorry

/-- The total functor of `toGroupoids.map f` is continuous for associated étale topologies. -/
instance toGroupoids_map_isContinuous_etale {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.IsContinuous
      F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor (toGroupoids.map f))
    (StandardTopology.etale.overTopology S)

/-- The total functor of `toGroupoids.map f` is cocontinuous for associated étale topologies. -/
instance toGroupoids_map_isCocontinuous_etale {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.IsCocontinuous
      F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor (toGroupoids.map f))
    (StandardTopology.etale.overTopology S)

/-- `smallEtaleToGroupoids` agrees with the identity-equivalence specialization of `u`. -/
theorem smallEtaleToGroupoids_eq_smallEtaleFunctor_id (F : AlgebraicSpace S) :
    smallEtaleToGroupoids F = GroupoidsOver.smallEtaleFunctor_id F :=
  sorry

/-- Type-valued restriction uses the same functor `u` as the base of `π_F`. -/
theorem restrictEtale_eq_pi_type (F : AlgebraicSpace S) :
    smallEtaleToGroupoids F =
      (GroupoidsOver.pi F F.toGroupoids
          (Bicategory.Equivalence.id F.toGroupoids)).base :=
  sorry

/-- The total functor of `toGroupoids.map f` is continuous for associated étale topologies. -/
instance toGroupoids_map_toFunctor_isContinuous_etale {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toFunctor (toGroupoids.map f)).IsContinuous
      F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology :=
  sorry

/-- The cartesian total functor of `toGroupoids.map f` agrees with `toFunctor`. -/
theorem toGroupoids_map_cartesian_eq {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor =
      toFunctor (toGroupoids.map f) :=
  congrArg (fun F => F.toFunctor)
    (toCartesianBasedFunctor.toBasedFunctor (toGroupoids.map f))

/-- Pointwise right Kan extensions exist for type-valued presheaves in universe `u`
along `toGroupoids.map f`. -/
instance toGroupoids_map_op_hasPointwiseRightKanExtension_type {F G : AlgebraicSpace S}
    (f : F ⟶ G) (P : F.toGroupoids.totalᵒᵖ ⥤ Type u) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions exist for ring-valued presheaves along `toGroupoids.map f`. -/
instance toGroupoids_map_op_hasPointwiseRightKanExtension_ring {F G : AlgebraicSpace S}
    (f : F ⟶ G) (P : F.toGroupoids.totalᵒᵖ ⥤ RingCat.{u}) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.HasPointwiseRightKanExtension P :=
  sorry

/-- Forgetting rings preserves the right Kan extensions used by CFG étale direct image. -/
instance toGroupoids_map_forget_preservesRightKanExtensions {F G : AlgebraicSpace S}
    (f : F ⟶ G) :
    (forget RingCat.{u}).PreservesRightKanExtensions
      (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op :=
  sorry

/-- The composite `toFunctor (toGroupoids.map f) ⋙ G.toGroupoids.p` is continuous
from `F_étale` to the big étale site of `S`. -/
instance toGroupoids_map_comp_p_isContinuous {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toFunctor (toGroupoids.map f) ⋙ G.toGroupoids.p).IsContinuous
      F.toGroupoids.etaleTopology (StandardTopology.etale.overTopology S) :=
  sorry

/-- Inverse-image form of the structure-sheaf map of `toGroupoids.map f`. -/
def toGroupoidsEtaleStructureSheafInv {F G : AlgebraicSpace S} (f : F ⟶ G) :
    ((toFunctor (toGroupoids.map f)).sheafPushforwardContinuous RingCat.{u}
        F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology).obj
      (GroupoidsOver.etaleRingedSite G.toGroupoids).structureSheaf ⟶
      (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf :=
  (sheafPushforwardContinuousIso (eqToIso (comm (toGroupoids.map f)).symm) RingCat.{u}
      F.toGroupoids.etaleTopology (StandardTopology.etale.overTopology S)).inv.app
    (StandardTopology.Big.structureSheaf StandardTopology.etale S)

/-- Direct-image form of the structure-sheaf map of `toGroupoids.map f`. -/
def toGroupoidsEtaleStructureSheafMap {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (GroupoidsOver.etaleRingedSite G.toGroupoids).structureSheaf ⟶
      ((toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.sheafPushforwardCocontinuous
          RingCat.{u} F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology).obj
        (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf :=
  ((toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.sheafAdjunctionCocontinuous
      RingCat.{u} F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology).homEquiv _ _
    (toGroupoidsEtaleStructureSheafInv f)

/-- The direct-image structure map of `toGroupoids.map f` preserves internal-ring operations. -/
theorem toGroupoidsEtaleStructureSheafMap_isRingCompatible {F G : AlgebraicSpace S}
    (f : F ⟶ G) :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (GroupoidsOver.etaleRingedSite F.toGroupoids)
      (GroupoidsOver.etaleRingedSite G.toGroupoids) inferInstance inferInstance
      ((toCartesianBasedFunctor (toGroupoids.map f)).morphismOfTopoiIn
        (StandardTopology.etale.overTopology S) :
        MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
          G.toGroupoids.etaleTopology F.toGroupoids.etaleTopology)
      ((toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.sheafPushforwardCocontinuous
        RingCat.{u} F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology)
      (Functor.sheafPushforwardCocontinuous.compSheafComposeIso
        (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor (forget RingCat.{u})
        F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology)
      (toGroupoidsEtaleStructureSheafMap f) :=
  sorry

/-- The morphism of étale ringed topoi induced by `toGroupoids.map f`. -/
def toGroupoidsEtaleRingedToposHom {F G : AlgebraicSpace S} (f : F ⟶ G) :
    RingedSite.ToposHom
      (GroupoidsOver.etaleRingedSite F.toGroupoids)
      (GroupoidsOver.etaleRingedSite G.toGroupoids) :=
  @RingedSite.ToposHom.ofDirectImage
    (GroupoidsOver.etaleRingedSite F.toGroupoids)
    (GroupoidsOver.etaleRingedSite G.toGroupoids)
    inferInstance inferInstance
    ((toCartesianBasedFunctor (toGroupoids.map f)).morphismOfTopoiIn
      (StandardTopology.etale.overTopology S) :
      MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
        G.toGroupoids.etaleTopology F.toGroupoids.etaleTopology)
    ((toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.sheafPushforwardCocontinuous
      RingCat.{u} F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology)
    (Functor.sheafPushforwardCocontinuous.compSheafComposeIso
      (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor (forget RingCat.{u})
      F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology)
    (toGroupoidsEtaleStructureSheafMap f)
    (toGroupoidsEtaleStructureSheafMap_isRingCompatible f)

/-- Direct image `f_*` of étale `𝒪`-modules along `toGroupoids.map f`. -/
def etaleModulePushforward {F G : AlgebraicSpace S} (f : F ⟶ G) :
    SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf ⥤
      SheafOfModules.{u} (GroupoidsOver.etaleRingedSite G.toGroupoids).structureSheaf :=
  (toGroupoidsEtaleRingedToposHom f).modulePushforward

/-- `etaleModulePushforward` is the module direct image of `toGroupoidsEtaleRingedToposHom`. -/
theorem etaleModulePushforward_eq {F G : AlgebraicSpace S} (f : F ⟶ G) :
    etaleModulePushforward f = (toGroupoidsEtaleRingedToposHom f).modulePushforward :=
  rfl

/-- Restriction of an étale `𝒪`-module on `S_F` to `F_étale`, as module pushforward
along `π_F` for the identity equivalence of `F.toGroupoids`. -/
def restrictEtaleModules (F : AlgebraicSpace S) :
    SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf ⥤
      SheafOfModules.{u} (structureSheaf F) :=
  (GroupoidsOver.pi F F.toGroupoids (Bicategory.Equivalence.id F.toGroupoids)).modulePushforward.{u}

/-- `restrictEtaleModules` is module pushforward along `π_F`. -/
theorem restrictEtaleModules_eq (F : AlgebraicSpace S) :
    restrictEtaleModules F =
      (GroupoidsOver.pi F F.toGroupoids
          (Bicategory.Equivalence.id F.toGroupoids)).modulePushforward.{u} :=
  rfl

/-- Underlying type-valued sheaf of an étale `𝒪`-module on `S_F`. -/
def moduleUnderlyingType {F : AlgebraicSpace S}
    (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf) :
    Sheaf F.toGroupoids.etaleTopology (Type u) :=
  (ToInternal.underlying (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf).obj ℳ

/-- `moduleUnderlyingType` is the forgetful image of an étale `𝒪`-module. -/
theorem moduleUnderlyingType_eq {F : AlgebraicSpace S}
    (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf) :
    moduleUnderlyingType ℳ =
      (ToInternal.underlying
          (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf).obj ℳ :=
  rfl

/-- Universe embedding of the underlying sheaf of an étale `𝒪`-module into the
`Type (u + 1)` étale sheaf category used by `compareBigSmall`. -/
def moduleUnderlyingULift {F : AlgebraicSpace S}
    (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf) :
    Sheaf F.toGroupoids.etaleTopology (Type (u + 1)) where
  obj := (moduleUnderlyingType ℳ).obj ⋙ uliftFunctor.{u + 1, u}
  property := sorry

/-- Objectwise, `moduleUnderlyingULift` is `ULift` of the underlying type of `ℳ`. -/
theorem moduleUnderlyingULift_obj {F : AlgebraicSpace S}
    (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf)
    (x : F.toGroupoids.totalᵒᵖ) :
    (moduleUnderlyingULift ℳ).obj.obj x = ULift.{u + 1, u} ((moduleUnderlyingType ℳ).obj.obj x) :=
  rfl

/-- Universe embedding of the underlying sheaf of a small-étale `𝒪`-module. -/
def smallEtaleModulesULift {H : AlgebraicSpace S} (N : H.Modules) :
    Sheaf (smallEtaleTopology H) (Type (u + 1)) where
  obj := ((ToInternal.underlying (structureSheaf H)).obj N).obj ⋙ uliftFunctor.{u + 1, u}
  property := sorry

/-- Objectwise, `smallEtaleModulesULift` is `ULift` of the underlying type. -/
theorem smallEtaleModulesULift_obj {H : AlgebraicSpace S} (N : H.Modules)
    (V : (smallEtaleSite H)ᵒᵖ) :
    (smallEtaleModulesULift N).obj.obj V =
      ULift.{u + 1, u} (((ToInternal.underlying (structureSheaf H)).obj N).obj.obj V) :=
  rfl

section CompareModules

variable {F G : AlgebraicSpace S} (f : F ⟶ G)
variable (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf)
variable [HasSheafify F.toGroupoids.etaleTopology (Type (u + 1))]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.HasPointwiseRightKanExtension P]

/-- Evaluation of the restricted CFG module pushforward at `V` recovers sections at `u(V)`. -/
def compareBigSmall_modules_leftEval (V : smallEtaleSite G) :
    ((ToInternal.underlying (structureSheaf G)).obj
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ))).obj.obj (op V) ≅
      ((ToInternal.underlying
          (GroupoidsOver.etaleRingedSite G.toGroupoids).structureSheaf).obj
        ((etaleModulePushforward f).obj ℳ)).obj.obj
          (op ((smallEtaleToGroupoids G).obj V)) :=
  Iso.refl _

/-- The Type-`u` comma diagram computing `f_*` of the underlying sheaf at `u_G(V)`. -/
abbrev compareBigDiagType (V : smallEtaleSite G) :
    compareBigIndex f V ⥤ Type u :=
  StructuredArrow.proj (op ((smallEtaleToGroupoids G).obj V))
      (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op ⋙
    (moduleUnderlyingType ℳ).obj

/-- The Type-`u` comma diagram computing `f_small,*` of the restricted underlying sheaf. -/
abbrev compareSmallDiagType (V : smallEtaleSite G) :
    compareSmallIndex f V ⥤ Type u :=
  StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion F).op ⋙
    ((ToInternal.underlying (structureSheaf F)).obj
      ((restrictEtaleModules F).obj ℳ)).obj

/-- Type-valued limits exist for the Type-`u` CFG Kan diagram. -/
instance compareBigDiagType_hasLimit (V : smallEtaleSite G) :
    HasLimit (compareBigDiagType f ℳ V) :=
  sorry

/-- Type-valued limits exist for the Type-`u` small-étale Kan diagram. -/
instance compareSmallDiagType_hasLimit (V : smallEtaleSite G) :
    HasLimit (compareSmallDiagType f ℳ V) :=
  sorry

/-- Type-valued limits exist after restriction along `compareIndexMap`. -/
instance compareIndexBigDiagType_hasLimit (V : smallEtaleSite G) :
    HasLimit (compareIndexMap f V ⋙ compareBigDiagType f ℳ V) :=
  sorry

/-- The Type-`u` Kan diagrams are identified after restriction along `compareIndexMap`. -/
def compareDiagIsoType (V : smallEtaleSite G) :
    compareIndexMap f V ⋙ compareBigDiagType f ℳ V ≅ compareSmallDiagType f ℳ V :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category, in universe `u`. -/
def compareLimitHomType (V : smallEtaleSite G) :
    limit (compareBigDiagType f ℳ V) ⟶ limit (compareSmallDiagType f ℳ V) :=
  limit.pre (compareBigDiagType f ℳ V) (compareIndexMap f V) ≫
    (HasLimit.isoOfNatIso (compareDiagIsoType f ℳ V)).hom

/-- Restriction of a small-étale compatible family to the atlas cover `U₀`, in universe `u`. -/
def compareCoverSectionType (V : smallEtaleSite G) :
    limit (compareSmallDiagType f ℳ V) ⟶
      (moduleUnderlyingType ℳ).obj.obj
        (op ((smallEtaleToGroupoids F).obj (coverSite f V))) :=
  (HasLimit.isoOfNatIso (compareDiagIsoType f ℳ V)).inv ≫
    limit.π (compareIndexMap f V ⋙ compareBigDiagType f ℳ V) (coverIndex f V)

/-- The family of sections of the underlying sheaf on `T ×_F U₀`. -/
def compareFibreSectionType (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiagType f ℳ V) ⟶
      (moduleUnderlyingType ℳ).obj.obj (op (compareFibreObj f j)) :=
  compareCoverSectionType f ℳ V ≫
    (moduleUnderlyingType ℳ).obj.map (compareFibreToCover f j).op

/-- Compatibility of the one-arrow covering family on `T ×_F U₀`, in universe `u`. -/
theorem compareFibreSectionType_compatible (V : smallEtaleSite G)
    (j : compareBigIndex f V) :
    ∀ ⦃W : F.toGroupoids.total⦄ ⦃i k : Unit⦄
      (a : W ⟶ compareFibreObj f j) (b : W ⟶ compareFibreObj f j),
      a ≫ compareFibreToBig f j = b ≫ compareFibreToBig f j →
        compareFibreSectionType f ℳ V j ≫ (moduleUnderlyingType ℳ).obj.map a.op =
          compareFibreSectionType f ℳ V j ≫ (moduleUnderlyingType ℳ).obj.map b.op :=
  sorry

/-- Component of the reverse Type-`u` comparison cone at a CFG comma object. -/
def compareInvπType (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiagType f ℳ V) ⟶ (compareBigDiagType f ℳ V).obj j :=
  (moduleUnderlyingType ℳ).property.amalgamateOfArrows
    (fun _ : Unit => compareFibreToBig f j)
    (compareFibre_cover_mem f j)
    (fun _ => compareFibreSectionType f ℳ V j)
    (compareFibreSectionType_compatible f ℳ V j)

/-- Extension of a small-étale compatible family to a CFG compatible family, in universe `u`. -/
def compareLimitInvType (V : smallEtaleSite G) :
    limit (compareSmallDiagType f ℳ V) ⟶ limit (compareBigDiagType f ℳ V) :=
  limit.lift (compareBigDiagType f ℳ V)
    { pt := limit (compareSmallDiagType f ℳ V)
      π :=
        { app := compareInvπType f ℳ V
          naturality := sorry } }

/-- Canonical identification of the two Type-`u` Kan-extension limits at `V`. -/
def compareLimitIsoType (V : smallEtaleSite G) :
    limit (compareBigDiagType f ℳ V) ≅ limit (compareSmallDiagType f ℳ V) where
  hom := compareLimitHomType f ℳ V
  inv := compareLimitInvType f ℳ V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Evaluation of the small étale module pushforward at `V` recovers the Type-`u`
Kan limit. -/
def compareBigSmall_modules_rightEval (V : smallEtaleSite G) :
    limit (compareSmallDiagType f ℳ V) ≅
      ((ToInternal.underlying (structureSheaf G)).obj
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ))).obj.obj (op V) :=
  ((smallEtaleInclusion F).op.ranObjObjIsoLimit
      ((ToInternal.underlying (structureSheaf F)).obj
        ((restrictEtaleModules F).obj ℳ)).obj
      (op ((etaleBaseChange f).obj V))).symm ≪≫
    ((sheafToPresheaf (smallEtaleTopology G) (Type u)).mapIso
        ((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).app
          ((restrictEtaleModules F).obj ℳ))).symm.app (op V)

/-- Sectionwise type-valued comparison underlying the `𝒪_G`-module identification. -/
def compareBigSmall_modules_app (V : smallEtaleSite G) :
    ((ToInternal.underlying (structureSheaf G)).obj
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ))).obj.obj (op V) ≅
      ((ToInternal.underlying (structureSheaf G)).obj
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ))).obj.obj (op V) :=
  compareBigSmall_modules_leftEval f ℳ V ≪≫
    ((sheafToPresheaf G.toGroupoids.etaleTopology (Type u)).mapIso
        ((RingedSite.ToposHom.ModulePushforward.forgetIso
            (toGroupoidsEtaleRingedToposHom f)).app ℳ)).app
      (op ((smallEtaleToGroupoids G).obj V)) ≪≫
      ((toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op.ranObjObjIsoLimit
          (moduleUnderlyingType ℳ).obj
          (op ((smallEtaleToGroupoids G).obj V))) ≪≫
        (compareLimitIsoType f ℳ V) ≪≫
          compareBigSmall_modules_rightEval f ℳ V

/-- Underlying type-valued morphism of the `𝒪_G`-module identification. -/
def compareBigSmall_modules_underlying :
    (ToInternal.underlying (structureSheaf G)).obj
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ)) ⟶
      (ToInternal.underlying (structureSheaf G)).obj
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ)) :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun V => (compareBigSmall_modules_app f ℳ V.unop).hom
      naturality := sorry }

/-- Inverse underlying type-valued morphism of the `𝒪_G`-module identification. -/
def compareBigSmall_modules_underlyingInv :
    (ToInternal.underlying (structureSheaf G)).obj
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ)) ⟶
      (ToInternal.underlying (structureSheaf G)).obj
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ)) :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun V => (compareBigSmall_modules_app f ℳ V.unop).inv
      naturality := sorry }

/-- The identification `(f_* ℳ)|_{G_étale} ≅ f_small,* (ℳ |_{F_étale})` as an
isomorphism of `𝒪_G`-modules on `G_étale`. -/
def compareBigSmall_modules :
    (restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ) ≅
      (Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ) where
  hom := homOfUnderlying (structureSheaf G)
    (compareBigSmall_modules_underlying f ℳ) sorry sorry
  inv := homOfUnderlying (structureSheaf G)
    (compareBigSmall_modules_underlyingInv f ℳ) sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- After universe embedding, the underlying sheaf of the left-hand `𝒪_G`-module
is the Type-`(u + 1)` restriction of the CFG pushforward. -/
theorem compareBigSmall_modules_spec :
    smallEtaleModulesULift
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ)) =
      (restrictEtale G).obj ((etalePushforward f).obj (moduleUnderlyingULift ℳ)) :=
  sorry

/-- After universe embedding, the underlying sheaf of the right-hand `𝒪_G`-module
is the Type-`(u + 1)` small étale pushforward of the restricted underlying sheaf. -/
theorem compareBigSmall_modules_spec_small :
    smallEtaleModulesULift
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ)) =
      (sheafPushforwardType f).obj ((restrictEtale F).obj (moduleUnderlyingULift ℳ)) :=
  sorry

/-- The underlying type-valued sheaf map of `compareBigSmall_modules` is
`compareBigSmall_modules_underlying`. -/
theorem compareBigSmall_modules_forget :
    (ToInternal.underlying (structureSheaf G)).map (compareBigSmall_modules f ℳ).hom =
      compareBigSmall_modules_underlying f ℳ :=
  sorry

/-- The forward map of `compareBigSmall_modules` is `𝒪_G`-linear. -/
theorem compareBigSmall_modules_isLinear (V : (smallEtaleSite G)ᵒᵖ)
    (r : (structureSheaf G).obj.obj V)
    (x : ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ)).val.obj V) :
    (compareBigSmall_modules f ℳ).hom.val.app V (r • x) =
      r • (compareBigSmall_modules f ℳ).hom.val.app V x :=
  sorry

end CompareModules

end AlgebraicGeometry.AlgebraicSpace
