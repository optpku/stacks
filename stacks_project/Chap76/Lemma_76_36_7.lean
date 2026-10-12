/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Semicontinuity.Defs
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_30_1_ConnectedComponents

/-!
# Lower semicontinuity of geometric fibre-component counts of proper flat morphisms

The target-indexed geometric fibre-component count of a proper, flat morphism of
finite presentation of algebraic spaces is lower semicontinuous on the space of
points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.36.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper, flat
morphism of finite presentation of algebraic spaces over `S`. Let
`geometricFiberComponentCount f` be the function `n_{X/Y}` on `Points Y`
counting geometric connected components of fibres of `f` introduced in
Lemma 76.30.1. Then `geometricFiberComponentCount f` is lower semicontinuous. -/
@[stacks 0E1D]
theorem lowerSemicontinuous_geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f] :
    LowerSemicontinuous (geometricFiberComponentCount f) :=
  sorry

/-- The geometric fibre-component count of a proper, flat, finite-presentation
morphism of algebraic spaces is lower semicontinuous at a point of the target. -/
theorem lowerSemicontinuousAt_geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (y : Points Y) :
    LowerSemicontinuousAt (geometricFiberComponentCount f) y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
