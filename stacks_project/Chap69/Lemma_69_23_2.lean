/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Neighborhood
import StacksCheckRecall

/-!
# Finite neighbourhoods of finite geometric fibres of proper morphisms

A proper morphism of algebraic spaces over a locally Noetherian target whose
geometric fibre over a geometric point is finite is finite over some open
neighbourhood of that geometric point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 69.23.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `ybar` be a geometric point of `Y`. Assume `Y`
is locally Noetherian, `f` is proper, and `|X_ybar|` is finite. Then there
exists an open neighbourhood `V ⊂ Y` of `ybar` such that
`openInverseImageTo f ι : openInverseImage f ι ⟶ V` is finite.

The open neighbourhood is an open immersion `ι : V ⟶ Y` with
`ybar.image ∈ Set.range (Points.map ι)`, the restricted morphism is
`openInverseImageTo f ι`, and finiteness of `|X_ybar|` is
`Finite (Points (fieldFiber f ybar.toFieldValuedPoint))`. A more general
version without local Noetherianity, using quasi-finiteness at ordinary
points over `y`, is Lemma 76.35.2. -/
@[stacks 0A4W] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isFinite_openInverseImageTo_of_finite_fieldFiber :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
      (f : X ⟶ Y) [Proper f] (ybar : GeometricPoint Y),
      Finite (Points (fieldFiber f ybar.toFieldValuedPoint)) →
    ∃ (V : AlgebraicSpace S) (ι : V ⟶ Y) (hι : IsOpenImmersion ι),
      ybar.image ∈ Set.range (Points.map ι) ∧
        IsFinite (openInverseImageTo f ι))

end AlgebraicGeometry.AlgebraicSpace
