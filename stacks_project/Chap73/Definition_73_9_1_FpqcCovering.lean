/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange

/-!
# Fpqc covering families of algebraic spaces

An fpqc covering of an algebraic space is a pointwise flat indexed family of
morphisms such that every test morphism from an affine scheme admits a standard
fpqc cover refining the pullback family.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The pullback family `{X_i ×_X Z ⟶ Z}` of an indexed family over `X` along a
morphism `h : ofOver Z ⟶ X`. -/
def pullbackFamily {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X) {Z : Over S} (h : ofOver Z ⟶ X) :
    ι → Over (ofOver Z) :=
  fun i ↦ (overPullback h).obj (family i)

/-- The structure morphism of `pullbackFamily family h i` is the slice base
change of `family i` along `h`. -/
theorem pullbackFamily_hom {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X) {Z : Over S} (h : ofOver Z ⟶ X) (i : ι) :
    (pullbackFamily family h i).hom = overPullbackSnd h (family i) :=
  sorry

/-- The morphism of algebraic spaces over `S` induced by a chart of a standard
fpqc cover of an affine scheme `Z` over `S`. -/
def ofStandardFpqcCoverMap {S : Scheme.{u}} {Z : Over S}
    (𝒰 : StandardFpqcCover Z.left) (j : Fin 𝒰.n) :
    ofOver (Over.mk (𝒰.map j ≫ Z.hom)) ⟶ ofOver Z :=
  ofOverMap (Over.homMk (𝒰.map j) rfl : Over.mk (𝒰.map j ≫ Z.hom) ⟶ Z)

/-- `ofStandardFpqcCoverMap 𝒰 j` is `ofOverMap` of the corresponding morphism
in `Over S`. -/
theorem ofStandardFpqcCoverMap_eq {S : Scheme.{u}} {Z : Over S}
    (𝒰 : StandardFpqcCover Z.left) (j : Fin 𝒰.n) :
    ofStandardFpqcCoverMap 𝒰 j =
      ofOverMap (Over.homMk (𝒰.map j) rfl : Over.mk (𝒰.map j ≫ Z.hom) ⟶ Z) :=
  sorry

/-- A scheme-level standard fpqc cover of `Z`, viewed as a family of morphisms
of algebraic spaces over `ofOver Z`. -/
def ofStandardFpqcCover {S : Scheme.{u}} {Z : Over S}
    (𝒰 : StandardFpqcCover Z.left) :
    SemiRepresentableFamily.Over (ofOver Z) :=
  SemiRepresentableFamily.Over.ofArrows
    (fun j : Fin 𝒰.n ↦ ofOver (Over.mk (𝒰.map j ≫ Z.hom)))
    (fun j : Fin 𝒰.n ↦ ofStandardFpqcCoverMap 𝒰 j)

/-- The `j`-th object of `ofStandardFpqcCover 𝒰` is the chart morphism of
algebraic spaces associated to `𝒰.map j`. -/
theorem ofStandardFpqcCover_obj {S : Scheme.{u}} {Z : Over S}
    (𝒰 : StandardFpqcCover Z.left) (j : Fin 𝒰.n) :
    (ofStandardFpqcCover 𝒰).obj j = Over.mk (ofStandardFpqcCoverMap 𝒰 j) :=
  sorry

/-- An indexed family of morphisms of algebraic spaces with target `X` is an
fpqc covering when each member is flat and every morphism from an affine scheme
to `X` admits a standard fpqc cover refining the pullback family. -/
structure FpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X) : Prop where
  /-- Each member of the family is a flat morphism of algebraic spaces. -/
  flat : ∀ i, Flat (family i).hom
  /-- Every morphism from an affine scheme to `X` admits a standard fpqc cover
  refining the pulled-back family `{X_i ×_X Z ⟶ Z}`. -/
  exists_standardRefinement :
    ∀ {Z : Over S}, IsAffine Z.left → ∀ (h : ofOver Z ⟶ X),
      ∃ 𝒰 : StandardFpqcCover Z.left,
        SemiRepresentableFamily.Over.Refines (ofStandardFpqcCover 𝒰)
          { index := ι, obj := pullbackFamily family h }

namespace FpqcCovering

/-- Pack memberwise flatness and the standard affine-refinement condition into
an fpqc covering family. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X) (hflat : ∀ i, Flat (family i).hom)
    (hrefine :
      ∀ {Z : Over S}, IsAffine Z.left → ∀ (h : ofOver Z ⟶ X),
        ∃ 𝒰 : StandardFpqcCover Z.left,
          SemiRepresentableFamily.Over.Refines (ofStandardFpqcCover 𝒰)
            { index := ι, obj := pullbackFamily family h }) :
    FpqcCovering family where
  flat := hflat
  exists_standardRefinement := hrefine

/-- An indexed family is an fpqc covering if and only if it is pointwise flat
and every morphism from an affine scheme to the target admits a standard fpqc
cover refining the pullback family. -/
theorem iff {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X) :
    FpqcCovering family ↔
      (∀ i, Flat (family i).hom) ∧
        ∀ {Z : Over S}, IsAffine Z.left → ∀ (h : ofOver Z ⟶ X),
          ∃ 𝒰 : StandardFpqcCover Z.left,
            SemiRepresentableFamily.Over.Refines (ofStandardFpqcCover 𝒰)
              { index := ι, obj := pullbackFamily family h } :=
  sorry

/-- An fpqc covering consists of flat members together with a standard fpqc
refinement of every affine pullback family. -/
theorem source_spec {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over X} (hfam : FpqcCovering family) :
    (∀ i, Flat (family i).hom) ∧
      ∀ {Z : Over S}, IsAffine Z.left → ∀ (h : ofOver Z ⟶ X),
        ∃ 𝒰 : StandardFpqcCover Z.left,
          SemiRepresentableFamily.Over.Refines (ofStandardFpqcCover 𝒰)
            { index := ι, obj := pullbackFamily family h } :=
  sorry

/-- Equivalently, there are indices `i_j` and morphisms `Z_j ⟶ X_{i_j}` making
the triangles over `X` commute. -/
theorem exists_indices {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over X} (hfam : FpqcCovering family) {Z : Over S}
    (hZ : IsAffine Z.left) (h : ofOver Z ⟶ X) :
    ∃ (𝒰 : StandardFpqcCover Z.left) (α : Fin 𝒰.n → ι)
      (φ : ∀ j, ofOver (Over.mk (𝒰.map j ≫ Z.hom)) ⟶ (family (α j)).left),
      ∀ j, φ j ≫ (family (α j)).hom = ofStandardFpqcCoverMap 𝒰 j ≫ h :=
  sorry

end FpqcCovering

/-- If `X` and every `X_i` are representable, an fpqc covering of algebraic
spaces is the same as an fpqc covering of schemes. -/
theorem fpqcCovering_ofOver_iff {S : Scheme.{u}} {T : Over S} {ι : Type v}
    (U : ι → Over S) (f : ∀ i, U i ⟶ T) :
    FpqcCovering (fun i ↦ Over.mk (ofOverMap (f i))) ↔
      Scheme.FpqcCovering (fun i ↦ Over.mk (f i).left) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
