/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper.BaseChange

/-!
# Inverse images of closed subsets proper over a base

Properness of a closed subset of an algebraic space over a base is preserved by
topological inverse image along a cartesian square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver.preimage :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y},
    IsPullback g' f' f g →
      ∀ [LocallyOfFiniteType f] (T : Closeds (Points X)),
        ProperOver f T → ProperOver f' (T.preimage (Points.continuous_map g')))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver.preimage_pullback :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [HasPullback f g] [LocallyOfFiniteType f]
    (T : Closeds (Points X)),
    ProperOver f T → ProperOver (pullback.snd f g)
      (T.preimage (Points.continuous_map (pullback.fst f g))))

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
