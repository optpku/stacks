module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 73.9.1: Let `S` be a scheme, and let `X` be an algebraic space over
`S`. An fpqc covering of `X` is a family of morphisms `{f_i : X_i ⟶ X}_{i ∈ I}`
of algebraic spaces such that each `f_i` is flat and such that for every affine
scheme `Z` and morphism `h : Z ⟶ X` there exists a standard fpqc covering
`{g_j : Z_j ⟶ Z}` which refines the family `{X_i ×_X Z ⟶ Z}_{i ∈ I}`. -/
@[stacks 03MQ] #check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering :
  {S : AlgebraicGeometry.Scheme.{u}} → {X : AlgebraicGeometry.AlgebraicSpace S} →
    {ι : Type v} → (ι → CategoryTheory.Over X) → Prop)

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X),
    FpqcCovering family ↔
      (∀ i, Flat (family i).hom) ∧
        ∀ {Z : Over S}, IsAffine Z.left → ∀ (h : ofOver Z ⟶ X),
          ∃ 𝒰 : StandardFpqcCover Z.left,
            SemiRepresentableFamily.Over.Refines (ofStandardFpqcCover 𝒰)
              { index := ι, obj := pullbackFamily family h })
