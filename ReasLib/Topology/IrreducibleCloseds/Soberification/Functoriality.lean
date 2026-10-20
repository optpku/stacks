/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.IrreducibleCloseds.Soberification.Basic

/-!
# Functoriality of the Irreducible-Closed Soberification

Continuous maps induce continuous maps between soberifications, naturally with
respect to the point-closure maps.
-/

@[expose] public section

universe u v w

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

section

variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

/-- The inverse image of a soberification basic open under the map on irreducible closed subsets
is the basic open associated to the inverse image in the source. -/
theorem IrreducibleCloseds.preimage_basicOpen_map (f : C(X, Y)) (U : Opens Y) :
    IrreducibleCloseds.map f f.continuous ⁻¹' IrreducibleCloseds.basicOpen U =
      IrreducibleCloseds.basicOpen (Opens.comap f U) := sorry

/-- The map on irreducible closed subsets induced by a continuous map is continuous for the
soberification topologies. -/
theorem IrreducibleCloseds.continuous_map (f : C(X, Y)) :
    Continuous (IrreducibleCloseds.map f f.continuous :
      IrreducibleCloseds X → IrreducibleCloseds Y) := sorry

/-- The continuous map on soberifications induced by a continuous map. -/
def IrreducibleCloseds.mapContinuous (f : C(X, Y)) :
    C(IrreducibleCloseds X, IrreducibleCloseds Y) :=
  ⟨IrreducibleCloseds.map f f.continuous, IrreducibleCloseds.continuous_map f⟩

/-- Evaluation of the continuous map induced on irreducible closed subsets. -/
@[simp]
theorem IrreducibleCloseds.mapContinuous_apply (f : C(X, Y))
    (T : IrreducibleCloseds X) :
    IrreducibleCloseds.mapContinuous f T =
      IrreducibleCloseds.map f f.continuous T := sorry

/-- Mapping the irreducible point closure of `x` along `f` gives the irreducible point closure
of `f x`. -/
@[simp]
theorem IrreducibleCloseds.mapContinuous_toIrreducibleCloseds
    (f : C(X, Y)) (x : X) :
    IrreducibleCloseds.mapContinuous f (toIrreducibleCloseds x) =
      toIrreducibleCloseds (f x) := sorry

/-- Soberification sends the identity continuous map to the identity continuous map. -/
@[simp]
theorem IrreducibleCloseds.mapContinuous_id :
    IrreducibleCloseds.mapContinuous (ContinuousMap.id X) =
      ContinuousMap.id (IrreducibleCloseds X) := sorry

/-- Soberification sends a composite to the composite of the induced continuous maps. -/
@[simp]
theorem IrreducibleCloseds.mapContinuous_comp (g : C(Y, Z)) (f : C(X, Y)) :
    IrreducibleCloseds.mapContinuous (g.comp f) =
      (IrreducibleCloseds.mapContinuous g).comp (IrreducibleCloseds.mapContinuous f) := sorry

end
