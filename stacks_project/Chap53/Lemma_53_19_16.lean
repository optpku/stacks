/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.Properties
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.19.16 (1): a locally algebraic, equidimensional `k`-scheme of dimension one
with at-worst-nodal singularities is Gorenstein. -/
@[stacks 0E37] #check (AlgebraicGeometry.SchemeOverField.instGorensteinOfAtWorstNodal :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left] [Fact (topologicalKrullDim X.left = 1)]
    [Fact (atWorstNodal X)], Scheme.Gorenstein X.left)

/- Lemma 53.19.16 (2): a locally algebraic, equidimensional `k`-scheme of dimension one
with at-worst-nodal singularities is geometrically reduced over `k`. -/
@[stacks 0E37] #check (AlgebraicGeometry.SchemeOverField.instGeometricallyReducedOfAtWorstNodal :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left] [Fact (topologicalKrullDim X.left = 1)]
    [Fact (atWorstNodal X)], GeometricallyReduced X.hom)

end AlgebraicGeometry.SchemeOverField
