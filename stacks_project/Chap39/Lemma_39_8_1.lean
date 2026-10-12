/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Dimension

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

/- Lemma 39.8.1 (1): a locally algebraic group scheme over a field is equidimensional. -/
@[stacks 045X] #check
  (AlgebraicGeometry.GroupScheme.instEquidimensionalSpace :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G],
      EquidimensionalSpace G.left)

/- Lemma 39.8.1 (2): the global dimension of a locally algebraic group scheme equals its local
dimension at every point. -/
@[stacks 045X] #check
  (AlgebraicGeometry.GroupScheme.topologicalKrullDim_eq_topologicalKrullDimAt :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G]
      (g : G.left),
      topologicalKrullDim G.left = topologicalKrullDimAt g)

/- Lemma 39.8.1 (3): at a closed point of a locally algebraic group scheme, the global dimension
equals the Krull dimension of the stalk. -/
@[stacks 045X] #check
  (AlgebraicGeometry.GroupScheme.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G]
      (g : G.left),
      IsClosed ({g} : Set G.left) →
        topologicalKrullDim G.left = ringKrullDim (SchemeOverField.stalkRing G g))
