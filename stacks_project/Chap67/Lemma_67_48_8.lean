module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Coproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.48.8: if `f : Y ⟶ X` is a quasi-compact and quasi-separated morphism of
algebraic spaces over a scheme `S` and `Y` is the disjoint union of `Y₁` and `Y₂`,
then the coproduct of the normalizations of `X` in `Y₁` and in `Y₂` is the
normalization of `X` in `Y`. -/
@[stacks 0824] #check
  (AlgebraicGeometry.AlgebraicSpace.isNormalization_coprod :
    ∀ {S : Scheme.{u}} {X Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
      (f : Y ⟶ X) (ι₁ : Y₁ ⟶ Y) (ι₂ : Y₂ ⟶ Y)
      (hY : IsColimit (BinaryCofan.mk ι₁ ι₂))
      [QuasiCompact f] [QuasiSeparated f]
      [QuasiCompact (ι₁ ≫ f)] [QuasiSeparated (ι₁ ≫ f)]
      [QuasiCompact (ι₂ ≫ f)] [QuasiSeparated (ι₂ ≫ f)]
      (to₁ : Y₁ ⟶ X₁) (from₁ : X₁ ⟶ X) (to₂ : Y₂ ⟶ X₂) (from₂ : X₂ ⟶ X),
      IsNormalization (ι₁ ≫ f) to₁ from₁ →
        IsNormalization (ι₂ ≫ f) to₂ from₂ →
          IsNormalization f (normalizationCoproductTo hY to₁ to₂)
            (normalizationCoproductFrom from₁ from₂))

end AlgebraicGeometry.AlgebraicSpace
