/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X)

/- Definition 66.10.2: for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, the dimension of the local ring of `X` at `x` is `localRingDimAt x`, the unique
nonnegative `d` in the ambient type `WithBot ℕ∞` satisfying the equivalent conditions of
Lemma 66.10.1. Thus its value is a natural number or infinity. In this case `x` is also a
point of codimension `d` on `X`, meaning `localRingDimAt x = d`. -/
@[stacks 04NA] #check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt x : WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_nonneg x : 0 ≤ localRingDimAt x)

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_ringKrullDim_stalk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f) (u : U.left)
    {x : Points X} (hx : Points.mapOfOver f u = x),
    localRingDimAt x = ringKrullDim (U.left.presheaf.stalk u))
