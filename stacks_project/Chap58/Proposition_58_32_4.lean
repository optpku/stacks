module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.ClosedImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Proposition 58.32.4: a closed immersion of connected affine schemes over `𝔽ₚ` induces an
injective map `π₁(Z, z̄) → π₁(X, z̄)` at every geometric point of `Z`. -/
@[stacks 0G1I] #check
  (AlgebraicGeometry.SchemeOverField.fundamentalGroupMap_injective_of_isClosedImmersion :
    ∀ {p : ℕ} [Fact p.Prime]
      {Z X : AlgebraicGeometry.SchemeOverField (ZMod p)}
      [IsAffine Z.left] [IsAffine X.left]
      [ConnectedSpace Z.left] [ConnectedSpace X.left]
      (i : Z ⟶ X) [IsClosedImmersion i.left]
      (zbar : AlgebraicGeometry.Scheme.GeometricPoint Z.left),
      Function.Injective
        (AlgebraicGeometry.Scheme.GeometricPoint.fundamentalGroupMap i.left zbar))
