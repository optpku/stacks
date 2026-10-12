/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Splitting
public import ReasLib.Topology.Maps.OpenQuotient
public import ReasLib.Topology.NowhereDense.FiniteUnion
public import ReasLib.Topology.NowhereDense.OpenCover

/-!
# Topological consequences of finite morphisms

This file records the behavior of nowhere dense closed subsets under finite
morphisms of schemes.
-/

@[expose] public section

open CategoryTheory
open scoped Topology

universe u

namespace AlgebraicGeometry.IsFinite

/-- The image of a closed nowhere dense subset under a finite morphism of schemes is nowhere
dense. -/
theorem isNowhereDense_image_of_isClosed
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (T : Set Y)
    (hT_closed : IsClosed T) (hT_nowhere : IsNowhereDense T) :
    IsNowhereDense (f '' T) := sorry

/-- If a point is the unique point of its fiber under a finite morphism, every neighborhood of
that point contains the inverse image of a neighborhood of its image. -/
@[stacks 05B8]
theorem exists_nhds_preimage_subset_of_fiber_eq_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (h_fiber : f ⁻¹' {f x} = {x}) (U : Set X) (hU : U ∈ 𝓝 x) :
    ∃ V : Set Y, V ∈ 𝓝 (f x) ∧ f ⁻¹' V ⊆ U := sorry

end AlgebraicGeometry.IsFinite
