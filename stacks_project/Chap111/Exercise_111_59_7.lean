/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.FiniteField
import StacksCheckRecall

universe u

/- Exercise 111.59.7: over a finite field `k` and for `1 < g`, there are finitely
many isomorphism classes of smooth projective curves over `k` of genus `g`.
Proper curves over a field are projective, so smooth proper curves give the same
class of objects, with isomorphisms taken over `k`. -/
@[stacks 0DT6] #check (AlgebraicGeometry.Curve.finiteSkeletonOfGenus :
  ∀ {k : Type u} [Field k] [Finite k] (g : ℕ), 1 < g →
    Finite (CategoryTheory.Skeleton (AlgebraicGeometry.Curve.SmoothProperOfGenus k g)))
