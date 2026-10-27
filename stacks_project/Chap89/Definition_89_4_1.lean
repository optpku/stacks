/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Pullback
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 89.4.1: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|` be a closed point. By Decent Spaces, Lemma 68.14.6 we can represent `x`
by a closed immersion `i : Spec(k) ⟶ X`. The blowing up `X' ⟶ X` of `X` at `x` means
the blowing up of `X` in the closed subspace `Z = i(Spec(k)) ⊂ X`. -/
@[stacks 0BHE] #check (AlgebraicGeometry.AlgebraicSpace.Blowup.atPoint :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (x : Points X) (hx : x ∈ closedPoints (Points X)), Type (u + 2))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofClosedPoint :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (x : Points X) (hx : x ∈ closedPoints (Points X)), ClosedSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.atPoint_eq :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
      (x : Points X) (hx : x ∈ closedPoints (Points X)),
      Blowup.atPoint x hx = Blowup.along (ClosedSubspace.ofClosedPoint x hx))
