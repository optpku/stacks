/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.QuasiAffineNormalization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 110.23.1: for a field `k` there exists a variety `X` over `k` whose
normalization is quasi-affine, while `X` itself is not quasi-affine. -/
@[stacks 0272] #check
  (AlgebraicGeometry.exists_variety_normalization_isQuasiAffine_not_isQuasiAffine :
    ∀ (k : Type u) [Field k],
    ∃ (X : SchemeOverField k),
      Variety X ∧
        (∀ [QuasiCompact (genericPointSpectrumCoproductTo X.left)]
          [QuasiSeparated (genericPointSpectrumCoproductTo X.left)],
          X.left.normalization.IsQuasiAffine) ∧
          ¬ X.left.IsQuasiAffine)

end AlgebraicGeometry
