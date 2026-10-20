/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
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

#check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → {ι : Type v} →
    (ι → Over X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X),
    FpqcCovering family ↔
      (∀ i, Flat (family i).hom) ∧
        ∀ {Z : Over S}, IsAffine Z.left → ∀ (h : ofOver Z ⟶ X),
          ∃ 𝒰 : StandardFpqcCover Z.left,
            SemiRepresentableFamily.Over.Refines (ofStandardFpqcCover 𝒰)
              { index := ι, obj := pullbackFamily family h })

#check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.exists_indices :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over X} (hfam : FpqcCovering family) {Z : Over S}
    (hZ : IsAffine Z.left) (h : ofOver Z ⟶ X),
    ∃ (𝒰 : StandardFpqcCover Z.left) (α : Fin 𝒰.n → ι)
      (φ : ∀ j, ofOver (Over.mk (𝒰.map j ≫ Z.hom)) ⟶ (family (α j)).left),
      ∀ j, φ j ≫ (family (α j)).hom = ofStandardFpqcCoverMap 𝒰 j ≫ h)

#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_ofOver_iff :
  ∀ {S : Scheme.{u}} {T : Over S} {ι : Type v}
    (U : ι → Over S) (f : ∀ i, U i ⟶ T),
    FpqcCovering (fun i ↦ Over.mk (ofOverMap (f i))) ↔
      Scheme.FpqcCovering (fun i ↦ Over.mk (f i).left))

end AlgebraicGeometry.AlgebraicSpace
