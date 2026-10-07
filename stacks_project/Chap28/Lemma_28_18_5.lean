module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.OpenImmersion
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 28.18.5: if `j : U ⟶ V` is an open immersion of quasi-affine schemes, then the square
formed by `j`, the canonical maps `U.toSpecΓ` and `V.toSpecΓ`, and
`AlgebraicGeometry.Spec.map j.appTop` is cartesian. -/
@[stacks 0ARY] #check
  (AlgebraicGeometry.Scheme.isPullback_toSpecΓ_toSpecΓ_of_isOpenImmersion :
    ∀ {U V : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ V)
      [AlgebraicGeometry.IsOpenImmersion j] [U.IsQuasiAffine] [V.IsQuasiAffine],
      IsPullback j U.toSpecΓ V.toSpecΓ (AlgebraicGeometry.Spec.map j.appTop))
