/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.ConnectedComponents.Semicontinuity
import StacksCheckRecall

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

/- Lemma 76.36.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is proper, flat, and of finite
presentation, and the geometric fibres of `f` are reduced. Let
`geometricFiberComponentCount f` be the function `n_{X/S}` on `Points Y`
counting geometric connected components of fibres of `f` introduced in
Lemma 76.30.1. Then `geometricFiberComponentCount f` is locally constant.

The canonical ℕ∞ count represents the finite nonnegative integer count here:
proper geometric fibres are of finite type over a field, hence Noetherian,
and therefore have finitely many connected components. -/
@[stacks 0E1E] #check
  (AlgebraicGeometry.AlgebraicSpace.isLocallyConstant_geometricFiberComponentCount :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [Proper f] → [Flat f] → [FinitePresentation f] →
      geometricallyReducedFiberLocus f = Set.univ →
      IsLocallyConstant (geometricFiberComponentCount f))

/- The geometric fibre-component count of a proper, flat, finite-presentation
morphism of algebraic spaces with reduced geometric fibres is locally constant
at a point of the target. -/
#check (AlgebraicGeometry.AlgebraicSpace.eventually_eq_geometricFiberComponentCount :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [Proper f] → [Flat f] → [FinitePresentation f] →
    geometricallyReducedFiberLocus f = Set.univ → ∀ (y : Points Y),
    ∀ᶠ y' in 𝓝 y, geometricFiberComponentCount f y' = geometricFiberComponentCount f y)

end AlgebraicGeometry.AlgebraicSpace
