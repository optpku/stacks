/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.DimensionOne.FiniteComponents

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Proposition 33.42.7: a finite set of points in a separated scheme whose quasi-compact opens
have finitely many irreducible components is contained in an affine open when the stalks at those
points are Noetherian of Krull dimension at most one. -/
@[stacks 09NN] #check
  (AlgebraicGeometry.Scheme.AffineOpen.DimensionOne.exists_containing_finiteSet :
    ∀ {X : Scheme.{u}} [X.IsSeparated]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (S : Set X) (_ : S.Finite)
      (_ : ∀ x : X, x ∈ S → IsNoetherianRing (X.presheaf.stalk x))
      (_ : ∀ x : X, x ∈ S → ringKrullDim (X.presheaf.stalk x) ≤ 1),
      ∃ U : X.affineOpens, S ⊆ ((U : X.Opens) : Set X))
