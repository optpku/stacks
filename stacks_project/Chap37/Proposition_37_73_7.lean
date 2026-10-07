module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineStratification

@[expose] public section

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineStratification

/- Proposition 37.73.7: the cohomology of a quasi-coherent module on a nonempty
quasi-compact quasi-separated scheme vanishes in every degree strictly above its affine
stratification number. -/
@[stacks 0F2Y] #check
  (AlgebraicGeometry.Scheme.FiniteAffineStratification.cohomology_isZero_of_number_lt :
    ∀ {X : Scheme.{u}} [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ), number X < p →
        IsZero (Scheme.Modules.cohomology ℱ p))

end AlgebraicGeometry.Scheme.FiniteAffineStratification
