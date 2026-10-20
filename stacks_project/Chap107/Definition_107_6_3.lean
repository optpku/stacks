/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.LocalRingAtPoint
import StacksCheckRecall

@[expose]
public section

open AlgebraicGeometry

universe u

/- Definition 107.6.3: let `X` be a locally Noetherian algebraic stack and let
`x ∈ |X|` be a finite type point. Its local-ring dimension is the integer `d`
characterized by the equivalent conditions of Lemma 107.6.2: some, equivalently
every, smooth scheme neighbourhood `(U, u)` of `x` satisfies
`2 dim 𝒪_{U, ū} - dim 𝒪_{R, e(ū)} = d`. Here these are étale local rings at a
geometric point `ū` above `u`, and `R = U ×_X U` with diagonal `e`. -/
@[stacks 0DSA] #check (AlgebraicGeometry.AlgebraicStack.localRingDimAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsLocallyNoetherian X] (x : AlgebraicStack.Points X),
    AlgebraicStack.IsFiniteTypePoint x → EInt)

#check (AlgebraicGeometry.AlgebraicStack.localRingDimAt_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsLocallyNoetherian X] {x : AlgebraicStack.Points X}
    (hx : AlgebraicStack.IsFiniteTypePoint x) (d : ℤ),
    AlgebraicStack.localRingDimAt x hx = d ↔
      ∃ c : AlgebraicStack.SmoothSchemeChart x, c.localRingDimDiff = d)

#check (AlgebraicGeometry.AlgebraicStack.localRingDimAt_iff_forall :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsLocallyNoetherian X] {x : AlgebraicStack.Points X}
    (hx : AlgebraicStack.IsFiniteTypePoint x) (d : ℤ),
    AlgebraicStack.localRingDimAt x hx = d ↔
      ∀ c : AlgebraicStack.SmoothSchemeChart x, c.localRingDimDiff = d)

#check (AlgebraicGeometry.AlgebraicStack.localRingDimAt_eq_int :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsLocallyNoetherian X] {x : AlgebraicStack.Points X}
    (hx : AlgebraicStack.IsFiniteTypePoint x),
    ∃ n : ℤ, AlgebraicStack.localRingDimAt x hx = n)
