/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Fpqc covering families of algebraic spaces

An fpqc covering of an algebraic space is a pointwise flat indexed family of
morphisms such that every test morphism from an affine scheme admits a standard
fpqc cover refining the pullback family.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The pullback family `{X_i ×_X Z ⟶ Z}` of an indexed family over `X` along a
morphism `h : ofOver Z ⟶ X`. -/
def pullbackFamily {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X) {Z : Over S} (h : ofOver Z ⟶ X) :
    ι → Over (ofOver Z) :=
  fun i ↦ Over.mk (pullback.fst h (family i).hom)

/-- The morphism of algebraic spaces over `S` induced by a chart of a standard
fpqc cover of an affine scheme `Z` over `S`. -/
def ofStandardFpqcCoverMap {S : Scheme.{u}} {Z : Over S}
    (𝒰 : StandardFpqcCover Z.left) (j : Fin 𝒰.n) :
    ofOver (Over.mk (𝒰.map j ≫ Z.hom)) ⟶ ofOver Z :=
  ofOverMap (Over.homMk (𝒰.map j) rfl : Over.mk (𝒰.map j ≫ Z.hom) ⟶ Z)

/-- A scheme-level standard fpqc cover of `Z`, viewed as a family of morphisms
of algebraic spaces over `ofOver Z`. -/
def ofStandardFpqcCover {S : Scheme.{u}} {Z : Over S}
    (𝒰 : StandardFpqcCover Z.left) :
    SemiRepresentableFamily.Over (ofOver Z) :=
  SemiRepresentableFamily.Over.ofArrows
    (fun j : Fin 𝒰.n ↦ ofOver (Over.mk (𝒰.map j ≫ Z.hom)))
    (fun j : Fin 𝒰.n ↦ ofStandardFpqcCoverMap 𝒰 j)

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
  ⟨fun h ↦ ⟨h.flat, h.exists_standardRefinement⟩,
    fun h ↦ ⟨h.1, h.2⟩⟩

/-- An fpqc covering consists of flat members together with a standard fpqc
refinement of every affine pullback family. -/
theorem source_spec {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over X} (hfam : FpqcCovering family) :
    (∀ i, Flat (family i).hom) ∧
      ∀ {Z : Over S}, IsAffine Z.left → ∀ (h : ofOver Z ⟶ X),
        ∃ 𝒰 : StandardFpqcCover Z.left,
          SemiRepresentableFamily.Over.Refines (ofStandardFpqcCover 𝒰)
            { index := ι, obj := pullbackFamily family h } :=
  ⟨hfam.flat, hfam.exists_standardRefinement⟩

end FpqcCovering

end AlgebraicGeometry.AlgebraicSpace
