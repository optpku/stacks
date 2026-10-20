module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.HodgeTopDifferential

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Lemma 50.20.3: for a smooth proper equidimensional scheme of dimension `d`
over a field, the zero-extended top Hodge differential is zero. -/
@[stacks 0FW6] #check (AlgebraicGeometry.Scheme.DeRham.topCohomologyDifferential_eq_zero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
      [IsProper X.hom] [EquidimensionalSpace X.left] (d : ℕ),
      topologicalKrullDim X.left = d →
        AlgebraicGeometry.Scheme.DeRham.topCohomologyDifferential X.hom d = 0)
