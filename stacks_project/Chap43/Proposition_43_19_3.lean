module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity.Positivity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Proposition 43.19.3: the local intersection multiplicity at every irreducible
component of a proper intersection of closed subvarieties in a nonsingular variety
is strictly positive. -/
@[stacks 0B0V] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.intersectionMultiplicity_pos :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
      [Scheme.Regular X.left] (V W : X.left.IdealSheafData)
      [Variety (Over.mk (V.subschemeι ≫ X.hom))]
      [Variety (Over.mk (W.subschemeι ≫ X.hom))]
      (_ : Closeds.IntersectProperly V.support W.support)
      (Z : irreducibleComponents (V ⊔ W).subscheme),
      0 < V.intersectionMultiplicity W (genericPoints.ofComponent Z))
