/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChange
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap65.Lemma_65_7_2_Pullback
public import stacks_project.Chap96.«96_10_3_1_Restriction»

/-!
# Geometry of the represented big-versus-small étale comparison

The original comma arrows, atlas, and its pullbacks supply actual source
geometry independent of direct-image coefficient universes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite FiberedCategoryOver.Groupoids
open CategoryTheory.CategoryOfElements CategoryTheory.Sheaf.InternalModule
open Limits.Types
open scoped Bicategory

noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The comma category computing `f_* ℱ` at the tautological object `u_G(V)`. -/
abbrev compareBigIndex {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :=
  StructuredArrow (op ((smallEtaleToGroupoids G).obj V))
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op

/-- The comma category computing `f_small,* (ℱ |_{F_étale})` at `V ×_G F`. -/
abbrev compareSmallIndex {F G : AlgebraicSpace S} (f : F ⟶ G) (V : smallEtaleSite G) :=
  StructuredArrow (op ((etaleBaseChange f).obj V)) (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces F).op

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
  StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces F).op ⋙
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
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces F).obj (coverSite f V) ⟶ (etaleBaseChange f).obj V :=
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

/-- The actual map from a CFG comma chart to the specified target scheme. -/
def compareBigToTarget {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) : compareBigDomain f j ⟶ V.left :=
  j.hom.unop.unop.val.unop

/-- The comma chart maps to `F ×_G V` using both its source section and its
specified arrow to `V`. -/
def compareBigToBaseChange {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    ofOver (compareBigDomain f j) ⟶ etaleBaseChangeSpace f V :=
  pullback.lift (homFunctor (compareBigToF f j))
    (homFunctor (ofOverMap (compareBigToTarget f j))) sorry

/-- Pull the atlas of `F ×_G V` back along the actual comma-chart map into that fibre. -/
def compareFibreScheme {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) : Over S :=
  pullbackOverAtlas (compareBigToBaseChange f j) (coverToBaseChange f V)
    (etaleBaseChangeSpace f V).representableDiagonal (𝟙 _) (𝟙 _)

/-- The projection `T ×_{F ×_G V} U₀ ⟶ T`. -/
def compareFibreToDomain {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    yoneda.obj (compareFibreScheme f j) ⟶ yoneda.obj (compareBigDomain f j) :=
  pullbackOverAtlasFst (compareBigToBaseChange f j) (coverToBaseChange f V)
    (etaleBaseChangeSpace f V).representableDiagonal (𝟙 _) (𝟙 _)

/-- The projection `T ×_{F ×_G V} U₀ ⟶ U₀`. -/
def compareFibreToCoverScheme {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    compareFibreScheme f j ⟶ coverScheme f V :=
  pullbackOverAtlasSnd (compareBigToBaseChange f j) (coverToBaseChange f V)
    (etaleBaseChangeSpace f V).representableDiagonal (𝟙 _) (𝟙 _)

/-- The morphism `T ×_{F ×_G V} U₀ ⟶ F`. -/
def compareFibreHom {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    ofOver (compareFibreScheme f j) ⟶ F :=
  yoneda.map (compareFibreToCoverScheme f j) ≫ coverHom f V

/-- The object of `S_F` classified by `T ×_{F ×_G V} U₀ ⟶ F`. -/
def compareFibreObj {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) : F.toGroupoids.total :=
  op ⟨op (compareFibreScheme f j),
    yonedaEquiv (compareFibreHom f j)⟩

/-- The morphism `T ×_{F ×_G V} U₀ ⟶ U₀` in `S_F`. -/
def compareFibreToCover {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    compareFibreObj f j ⟶ (smallEtaleToGroupoids F).obj (coverSite f V) :=
  (homMk
      (unop ((smallEtaleToGroupoids F).obj (coverSite f V)))
      (unop (compareFibreObj f j))
      (compareFibreToCoverScheme f j).op sorry).op

/-- The morphism `T ×_{F ×_G V} U₀ ⟶ T` in `S_F`. -/
def compareFibreToBig {F G : AlgebraicSpace S} (f : F ⟶ G) {V : smallEtaleSite G}
    (j : compareBigIndex f V) :
    compareFibreObj f j ⟶ j.right.unop :=
  (homMk
      (unop (j.right.unop))
      (unop (compareFibreObj f j))
      (yonedaEquiv (compareFibreToDomain f j)).op sorry).op

/-- The covering family `{T ×_{F ×_G V} U₀ ⟶ T}` is an étale covering in `S_F`. -/
theorem compareFibre_cover_mem {F G : AlgebraicSpace S} (f : F ⟶ G)
    {V : smallEtaleSite G} (j : compareBigIndex f V) :
    Sieve.ofArrows (fun _ : Unit => compareFibreObj f j)
        (fun _ => compareFibreToBig f j) ∈
      F.toGroupoids.etaleTopology (j.right.unop) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
