/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyConstant.Basic
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_29_3_ReducedFiberLocus
public import stacks_project.Chap76.Lemma_76_30_1_ConnectedComponents

/-!
# Local constancy of geometric fibre-component counts of proper flat morphisms

The target-indexed geometric fibre-component count of a proper, flat morphism of
finite presentation of algebraic spaces with reduced geometric fibres is locally
constant on the space of points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.36.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is proper, flat, and of finite
presentation, and the geometric fibres of `f` are reduced. Let
`geometricFiberComponentCount f` be the function `n_{X/S}` on `Points Y`
counting geometric connected components of fibres of `f` introduced in
Lemma 76.30.1. Then `geometricFiberComponentCount f` is locally constant. -/
@[stacks 0E1E]
theorem isLocallyConstant_geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (h_reduced : geometricallyReducedFiberLocus f = Set.univ) :
    IsLocallyConstant (geometricFiberComponentCount f) :=
  sorry

/-- The geometric fibre-component count of a proper, flat, finite-presentation
morphism of algebraic spaces with reduced geometric fibres is locally constant
at a point of the target. -/
theorem eventually_eq_geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (h_reduced : geometricallyReducedFiberLocus f = Set.univ) (y : Points Y) :
    ∀ᶠ y' in 𝓝 y, geometricFiberComponentCount f y' = geometricFiberComponentCount f y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
