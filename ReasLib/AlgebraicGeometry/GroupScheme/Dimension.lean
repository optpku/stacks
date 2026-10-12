/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic

/-!
# Dimensions of group schemes

Equidimensionality and dimension comparisons for locally algebraic group schemes over fields.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

/-- A locally algebraic group scheme over a field is equidimensional. -/
instance instEquidimensionalSpace
    (G : AlgebraicGeometry.SchemeOverField k) [GrpObj G]
    [AlgebraicGeometry.LocallyAlgebraic G] :
    EquidimensionalSpace G.left := sorry

/-- The global dimension of a locally algebraic group scheme over a field equals its local
dimension at every point. -/
theorem topologicalKrullDim_eq_topologicalKrullDimAt
    (G : AlgebraicGeometry.SchemeOverField k) [GrpObj G]
    [AlgebraicGeometry.LocallyAlgebraic G] (g : G.left) :
    topologicalKrullDim G.left = topologicalKrullDimAt g := sorry

/-- At a closed point of a locally algebraic group scheme over a field, the global dimension
equals the Krull dimension of the stalk. -/
theorem topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed
    (G : AlgebraicGeometry.SchemeOverField k) [GrpObj G]
    [AlgebraicGeometry.LocallyAlgebraic G] (g : G.left)
    (h_g : IsClosed ({g} : Set G.left)) :
    topologicalKrullDim G.left =
      ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing G g) := sorry

end AlgebraicGeometry.GroupScheme
