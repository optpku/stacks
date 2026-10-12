/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.ClosedSubscheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.19.17 (1): a reduced equidimensional one-dimensional closed subscheme of a
locally algebraic equidimensional one-dimensional at-worst-nodal scheme is at-worst-nodal. -/
@[stacks 0E38] #check
  (AlgebraicGeometry.SchemeOverField.atWorstNodal_of_reducedClosedSubscheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (hXdim : topologicalKrullDim X.left = 1) (hXnodal : atWorstNodal X)
    (Y : X.left.IdealSheafData) [IsReduced Y.subscheme]
    [EquidimensionalSpace Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1),
    atWorstNodal (Over.mk (Y.subschemeι ≫ X.hom)))

/- Lemma 53.19.17 (2): the scheme-theoretic intersection of `Y` with the closure of its open
complement is a disjoint union of spectra of finite separable extensions of `k`. -/
@[stacks 0E38] #check
  (AlgebraicGeometry.SchemeOverField.intersection_isDisjointUnionOfSpecFiniteSeparable :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (hXdim : topologicalKrullDim X.left = 1) (hXnodal : atWorstNodal X)
    (Y : X.left.IdealSheafData) [IsReduced Y.subscheme]
    [EquidimensionalSpace Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1),
    Nonempty
      (SchemeAsDisjointUnionOfSpecFiniteSeparable k
        (Over.mk
          ((Y ⊔ schemeTheoreticClosureIdeal Y.openComplement).subschemeι ≫ X.hom))))

/- Lemma 53.19.17 (3): every point of the scheme-theoretic intersection of `Y` with the closure
of its open complement is a node of `X`. -/
@[stacks 0E38] #check
  (AlgebraicGeometry.SchemeOverField.intersection_points_areNodes :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (hXdim : topologicalKrullDim X.left = 1) (hXnodal : atWorstNodal X)
    (Y : X.left.IdealSheafData) [IsReduced Y.subscheme]
    [EquidimensionalSpace Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1),
    ∀ p : (Y ⊔ schemeTheoreticClosureIdeal Y.openComplement).subscheme,
      isNode X ((Y ⊔ schemeTheoreticClosureIdeal Y.openComplement).subschemeι p))

/- Lemma 53.19.17 (4): the morphism from `Y` to `Spec(k)` is smooth at every point of the
scheme-theoretic intersection of `Y` with the closure of its open complement. -/
@[stacks 0E38] #check
  (AlgebraicGeometry.SchemeOverField.smoothAt_intersectionPoints :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (hXdim : topologicalKrullDim X.left = 1) (hXnodal : atWorstNodal X)
    (Y : X.left.IdealSheafData) [IsReduced Y.subscheme]
    [EquidimensionalSpace Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1),
    ∀ p : (Y ⊔ schemeTheoreticClosureIdeal Y.openComplement).subscheme,
      (Y.subschemeι ≫ X.hom).SmoothAt
        ((Scheme.IdealSheafData.inclusion
          (le_sup_left : Y ≤ Y ⊔ schemeTheoreticClosureIdeal Y.openComplement)) p))

end AlgebraicGeometry.SchemeOverField
