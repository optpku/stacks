/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GeneralLinear.UpperTriangular.Quotient
public import ReasLib.AlgebraicGeometry.GeneralLinear.UpperTriangular.Invariants
public import ReasLib.AlgebraicGeometry.GeneralLinear.UpperTriangular.Smooth

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalLeftAction

universe u

/- Example 39.23.1 (1): in the Zariski topology, the quotient sheaf `GL₂/B` is represented by
the projective line. -/
@[stacks 03BG] #check
  (AlgebraicGeometry.GLTwo.UpperTriangular.quotientComparison_zariski_isIso :
    ∀ (k : Type u) [Field k],
      IsIso (AlgebraicGeometry.GLTwo.UpperTriangular.quotientComparison k .zariski))

/- Example 39.23.1 (2): in the étale topology, the quotient sheaf `GL₂/B` is represented by
the projective line. -/
@[stacks 03BG] #check
  (AlgebraicGeometry.GLTwo.UpperTriangular.quotientComparison_etale_isIso :
    ∀ (k : Type u) [Field k],
      IsIso (AlgebraicGeometry.GLTwo.UpperTriangular.quotientComparison k .etale))

/- Example 39.23.1 (3): in the fppf topology, the quotient sheaf `GL₂/B` is represented by
the projective line. -/
@[stacks 03BG] #check
  (AlgebraicGeometry.GLTwo.UpperTriangular.quotientComparison_fppf_isIso :
    ∀ (k : Type u) [Field k],
      IsIso (AlgebraicGeometry.GLTwo.UpperTriangular.quotientComparison k .fppf))

/- Example 39.23.1 (4): the invariant regular functions are exactly the scalar functions from
the base field. -/
@[stacks 03BG] #check
  (AlgebraicGeometry.GLTwo.UpperTriangular.invariantRing_eq_scalars :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.GLTwo.UpperTriangular.invariantRing k =
        RingHom.range (algebraMap k (AlgebraicGeometry.GLTwo.coordinateRing k)))

/- Example 39.23.1 (5): the source map of the action groupoid is smooth of relative dimension
three. -/
@[stacks 03BG] #check
  (AlgebraicGeometry.GLTwo.UpperTriangular.relationSource_smoothOfRelativeDimension :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.SmoothOfRelativeDimension 3
        (AlgebraicGeometry.GLTwo.UpperTriangular.relation k).s.left)

/- Example 39.23.1 (6): the target map of the action groupoid is smooth of relative dimension
three. -/
@[stacks 03BG] #check
  (AlgebraicGeometry.GLTwo.UpperTriangular.relationTarget_smoothOfRelativeDimension :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.SmoothOfRelativeDimension 3
        (AlgebraicGeometry.GLTwo.UpperTriangular.relation k).t.left)

/- The closed subgroup in the quotient presentation is the upper-triangular subgroup of `GL₂`. -/
#check
  (AlgebraicGeometry.GLTwo.UpperTriangular.closedSubgroup :
    ∀ (k : Type u) [CommRing k],
      AlgebraicGeometry.Scheme.ClosedSubgroup
        (AlgebraicGeometry.GeneralLinear.schemeOver k (AlgebraicGeometry.GLTwo.index)))

/- The object scheme of the quotient relation is `GL₂`. -/
#check
  (AlgebraicGeometry.GLTwo.UpperTriangular.relation_U :
    ∀ (k : Type u) [CommRing k],
      (AlgebraicGeometry.GLTwo.UpperTriangular.relation k).U =
        (AlgebraicGeometry.GeneralLinear.groupScheme k
          (AlgebraicGeometry.GLTwo.index)).X)

/- The arrow scheme is canonically identified with `GL₂ ×ₖ B`. -/
#check
  (AlgebraicGeometry.GLTwo.UpperTriangular.arrowsIso :
    ∀ (k : Type u) [CommRing k],
      (AlgebraicGeometry.GLTwo.UpperTriangular.relation k).R ≅
        (AlgebraicGeometry.GeneralLinear.groupScheme k
          (AlgebraicGeometry.GLTwo.index)).X ⊗
          (AlgebraicGeometry.GLTwo.UpperTriangular.groupScheme k).X)
