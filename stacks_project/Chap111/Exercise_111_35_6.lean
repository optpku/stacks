module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.AffineLine
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/- Exercise 111.35.6 (1): for a closed point `x` of `AffineSpaceOverField k 1`,
the relative tangent dimension of `affineSpaceOverFieldHom k 1` at `x` is `1`. -/
@[stacks 029I] #check
  (AlgebraicGeometry.tangentDimensionAt_affineLine_closedPoint :
    ∀ {k : Type u} [Field k] (x : AffineSpaceOverField k 1),
      IsClosed {x} → tangentDimensionAt (affineSpaceOverFieldHom k 1) x = 1)

/- Exercise 111.35.6 (2): at the generic point of `AffineSpaceOverField k 1`,
the relative tangent dimension of `affineSpaceOverFieldHom k 1` is `1`. -/
@[stacks 029I] #check
  (AlgebraicGeometry.tangentDimensionAt_affineLine_genericPoint :
    ∀ {k : Type u} [Field k], tangentDimensionAt (affineSpaceOverFieldHom k 1)
      (genericPoint (AffineSpaceOverField k 1)) = 1)

/- Exercise 111.35.6 (3): for a closed point `x` of `AffineSpaceOverField k 1`,
viewed over `Spec ℤ` via `terminal.from`, the `κ(x)`-rank of
`tangentSpaceAt (terminal.from X) x` equals
`1 + Module.rank (Ω[k⁄ℤ] →ₗ[k] κ(x))`. -/
@[stacks 029I] #check
  (AlgebraicGeometry.rank_tangentSpaceAt_affineLine_overInt_closedPoint :
    ∀ {k : Type u} [Field k] (x : AffineSpaceOverField k 1), IsClosed {x} →
      Module.rank ((AffineSpaceOverField k 1).residueField x)
        (tangentSpaceAt (terminal.from (AffineSpaceOverField k 1)) x) =
      1 + Module.rank ((AffineSpaceOverField k 1).residueField x)
        (Ω[k⁄ℤ] →ₗ[k] (AffineSpaceOverField k 1).residueField x))

/- Exercise 111.35.6 (4): at the generic point of `AffineSpaceOverField k 1`,
viewed over `Spec ℤ` via `terminal.from`, the `κ(η)`-rank of
`tangentSpaceAt (terminal.from X) η` equals
`1 + Module.rank (Ω[k⁄ℤ] →ₗ[k] κ(η))`. -/
@[stacks 029I] #check
  (AlgebraicGeometry.rank_tangentSpaceAt_affineLine_overInt_genericPoint :
    ∀ {k : Type u} [Field k],
      Module.rank
        ((AffineSpaceOverField k 1).residueField (genericPoint (AffineSpaceOverField k 1)))
        (tangentSpaceAt (terminal.from (AffineSpaceOverField k 1))
          (genericPoint (AffineSpaceOverField k 1))) =
      1 + Module.rank
        ((AffineSpaceOverField k 1).residueField (genericPoint (AffineSpaceOverField k 1)))
        (Ω[k⁄ℤ] →ₗ[k]
          (AffineSpaceOverField k 1).residueField (genericPoint (AffineSpaceOverField k 1))))

end AlgebraicGeometry
