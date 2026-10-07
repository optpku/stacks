module

public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.Closed
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.WLocalAffine

universe u

/- 61.5.2.3: for a ring `A` and a finite subset `E ⊆ A`, the vanishing-pattern
strata assemble to a closed subscheme `closed E = ∐ stratum p` of
`scheme E = Spec(∏ A_Z^~)`, via `closedι`. -/
@[stacks 0971] #check
  (AlgebraicGeometry.Scheme.WLocalAffine.closedι :
    ∀ {A : Type u} [CommRing A] (E : Finset A),
      AlgebraicGeometry.Scheme.WLocalAffine.closed E ⟶
        AlgebraicGeometry.Scheme.WLocalAffine.scheme E)
