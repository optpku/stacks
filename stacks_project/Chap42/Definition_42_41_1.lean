module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.Degree

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Definition 42.41.1: For a proper scheme `X` over a field `k`, the degree
homomorphism on relative zero-dimensional Chow classes is proper pushforward to
`Spec k`, followed by the canonical identification with `ℤ`. -/
@[stacks 0AZ1] #check (AlgebraicGeometry.ChowGroup.degree :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
        inferInstance 0 →+ ℤ)

end AlgebraicGeometry
