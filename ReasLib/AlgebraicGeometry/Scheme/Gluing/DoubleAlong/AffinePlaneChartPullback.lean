module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.DoubledOrigin

/-- The fibre product of the two canonical affine-plane charts over the doubled-origin scheme. -/
noncomputable abbrev affinePlaneChartPullback (k : Type u) [Field k] : Scheme.{u} :=
  pullback (chartMap k 2 0) (chartMap k 2 1)

/-- Affineness of the doubled-origin affine-plane chart fibre product is equivalent to affineness
of the intersection of its two canonical charts. -/
theorem isAffine_affinePlaneChartPullback_iff_chart_inf (k : Type u) [Field k] :
    IsAffine (affinePlaneChartPullback k) ↔
      IsAffineOpen (chart k 2 0 ⊓ chart k 2 1) := sorry

/-- The fibre product of the two canonical affine-plane charts over the doubled-origin scheme is
not affine. -/
theorem not_isAffine_affinePlaneChartPullback (k : Type u) [Field k] :
    ¬ IsAffine (affinePlaneChartPullback k) := sorry

end AlgebraicGeometry.DoubledOrigin
