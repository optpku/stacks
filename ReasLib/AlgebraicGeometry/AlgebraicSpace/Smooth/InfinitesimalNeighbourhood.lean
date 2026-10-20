/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood

/-!
# Smoothness from infinitesimal neighbourhoods

A locally finite-type morphism of algebraic spaces to a locally Noetherian
target is smooth above a closed subspace if its base changes to all
infinitesimal neighbourhoods of that subspace are smooth.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood

/-- If every base change of a locally finite-type morphism of algebraic spaces
to an infinitesimal neighbourhood of a closed subspace of a locally Noetherian
target is smooth, then the morphism is smooth at every point lying above that
closed subspace. -/
theorem smoothAt_of_smooth_pullbacks {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    [∀ n : ℕ, Smooth (pullback.snd f (toAmbient i n))]
    (x : Points X) (hx : Points.map f x ∈ Set.range (Points.map i)) :
    SmoothAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood
