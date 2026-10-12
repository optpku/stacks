/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/- Remark 111.35.7: Exercise 111.35.6 explains why the tangent space of a
scheme `X` must be taken relative to a base `S` to get a good notion. For
`X = AffineSpaceOverField k 1`, `tangentDimensionAt (affineSpaceOverFieldHom k 1) x`
stays `1`, while `Module.rank (tangentSpaceAt (terminal.from X) x)` is strictly
larger whenever the extra Kähler rank `Module.rank (Ω[k⁄ℤ] →ₗ[k] κ(x))` is
nonzero. -/
@[stacks 02F3] #check (AlgebraicGeometry.tangentDimensionAt_affineLine_ne_rank_overInt :
    ∀ {k : Type u} [Field k] (x : AffineSpaceOverField k 1),
      Module.rank ((AffineSpaceOverField k 1).residueField x)
          (Ω[k⁄ℤ] →ₗ[k] (AffineSpaceOverField k 1).residueField x) ≠ 0 →
        (tangentDimensionAt (affineSpaceOverFieldHom k 1) x : Cardinal) ≠
          Module.rank ((AffineSpaceOverField k 1).residueField x)
            (tangentSpaceAt (terminal.from (AffineSpaceOverField k 1)) x))

end AlgebraicGeometry
