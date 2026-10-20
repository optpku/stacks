module

import Mathlib.AlgebraicGeometry.Normalization
import StacksCheckRecall

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Y₁ Y₂ : Scheme.{u}} (f : Y ⟶ X) (i₁ : Y₁ ⟶ Y) (i₂ : Y₂ ⟶ Y)
  (e : IsColimit (BinaryCofan.mk i₁ i₂))
  [QuasiCompact f] [QuasiSeparated f]
  [QuasiCompact i₁] [QuasiSeparated i₁] [QuasiCompact i₂] [QuasiSeparated i₂]

/- Lemma 29.53.10: if `f : Y ⟶ X` is quasi-compact and quasi-separated and `Y` is the disjoint
union of `Y₁` and `Y₂`, then the coproduct of the normalizations of `X` in `Y₁` and `Y₂` is the
normalization of `X` in `Y`. -/
@[stacks 03GO] #check
  (AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso f e :
    (i₁ ≫ f).normalization ⨿ (i₂ ≫ f).normalization ≅ f.normalization)

end AlgebraicGeometry.Scheme.Hom
