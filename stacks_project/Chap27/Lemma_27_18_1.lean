module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Affine

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 27.18.1: Given two relative projective-spectrum presentations over the same scheme and
a morphism of their graded algebra sheaves, there is a unique relative projective-spectrum map
whose restriction over every affine base open is the absolute projective-spectrum map induced on
sections. -/
@[stacks 07ZG] #check
  (AlgebraicGeometry.RelativeProjMap.existsUnique_of_affine :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : Scheme.Hom.RelativeProjPresentation pX)
      (Pℬ : Scheme.Hom.RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra),
      ∃! rφ : RelativeProjMap P𝒜 Pℬ φ,
        ∀ W : S.affineOpens,
          Nonempty (RelativeProjMap.AffineChartCompatibility P𝒜 Pℬ φ rφ W))
