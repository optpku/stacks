module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Over every field there exists a variety whose absolute normalization is
quasi-affine, although the variety itself is not quasi-affine. -/
@[stacks 0272]
theorem exists_variety_normalization_isQuasiAffine_not_isQuasiAffine
    (k : Type u) [Field k] :
    ∃ (X : SchemeOverField k),
      Variety X ∧
        (∀ [QuasiCompact (genericPointSpectrumCoproductTo X.left)]
          [QuasiSeparated (genericPointSpectrumCoproductTo X.left)],
          X.left.normalization.IsQuasiAffine) ∧
          ¬ X.left.IsQuasiAffine := sorry

end AlgebraicGeometry
