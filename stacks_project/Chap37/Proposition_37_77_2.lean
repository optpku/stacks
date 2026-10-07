module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification.Weighting
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineStratification

/- Proposition 37.77.2: the affine stratification number of a nonempty separated scheme
surjectively covered by an affine scheme via a quasi-finite morphism is at most the number of
distinct values of the fibre integral of any positive weighting. -/
@[stacks 0F3S] #check
  (AlgebraicGeometry.Scheme.FiniteAffineStratification.number_le_fiberIntegralValues :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y},
      [Surjective f] → [Hom.QuasiFinite f] → [IsAffine X] → [Y.IsSeparated] → [Nonempty Y] →
      ∀ {w : X → ℤ}, f.IsWeighting w → (∀ x : X, 0 < w x) →
        -- Local instance justification (proof-local temporary data): target compactness is induced by the given continuous surjection.
        letI : CompactSpace Y := Function.Surjective.compactSpace f.continuous f.surjective
        number Y ≤
          (Set.range (f.fiberIntegral (Hom.tendstoCofinite_of_compactSource f) w)).ncard)

end AlgebraicGeometry.Scheme.FiniteAffineStratification
