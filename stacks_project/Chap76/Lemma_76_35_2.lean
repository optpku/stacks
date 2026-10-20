/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Neighborhood
import StacksCheckRecall

/-!
# Finite neighbourhoods of quasi-finite fibres of proper morphisms

A proper morphism of algebraic spaces that is quasi-finite at every point
over a given point of the target is finite over some open neighbourhood of
that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.35.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `y : Points Y`. Assume `f` is proper, and `f`
is quasi-finite at all `x : Points X` lying over `y`. Then there exists an
open neighbourhood `V ⊂ Y` of `y` such that
`openInverseImageTo f ι : openInverseImage f ι ⟶ V` is finite.

The open neighbourhood is an open immersion `ι : V ⟶ Y` with
`y ∈ Set.range (Points.map ι)`, and the restricted morphism is
`openInverseImageTo f ι`. Quasi-finiteness at points of `X` is
`QuasiFiniteAt` in the sense of Stacks 67.27.1 (2). -/
@[stacks 0A4Y] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isFinite_openInverseImageTo_of_quasiFiniteAt_fiber :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (y : Points Y)
    (h : ∀ x : Points X, Points.map f x = y → QuasiFiniteAt f x),
    ∃ (V : AlgebraicSpace S) (ι : V ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι))

end AlgebraicGeometry.AlgebraicSpace
