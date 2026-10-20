/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Category.Profinite.Basic
public import ReasLib.Topology.Category.Profinite.Recognition
public import ReasLib.Topology.ConstructibleTopology.Specialization

/-!
# Profinite Criteria for Spectral Spaces

This module packages the equivalent separation, specialization, and
constructible-topology criteria for a spectral space to be profinite.
@stack 0905
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

namespace SpectralSpace

/-- A spectral space has a profinite model exactly when it is Hausdorff. -/
@[stacks 0905 "profinite iff Hausdorff"]
theorem profinite_iff_t2Space (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    (∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) ↔ T2Space X := sorry

/-- For a spectral space, Hausdorffness is equivalent to total
disconnectedness. -/
@[stacks 0905 "Hausdorff iff totally disconnected"]
theorem t2Space_iff_totallyDisconnectedSpace (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ TotallyDisconnectedSpace X := sorry

/-- For a spectral space, Hausdorffness is equivalent to every compact open
subset being closed. -/
@[stacks 0905 "Hausdorff iff compact opens are closed"]
theorem t2Space_iff_compactOpen_isClosed (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ ∀ U : CompactOpens X, IsClosed (U : Set X) := sorry

/-- For a spectral space, Hausdorffness is equivalent to every open compact subset being closed.
This is the unbundled-set formulation used when compact opens arise from a construction rather
than as elements of `CompactOpens X`. -/
@[stacks 0905 "Hausdorff iff open compact subsets are closed"]
theorem t2Space_iff_forall_isOpen_isCompact_isClosed (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U := sorry

/-- For a spectral space, Hausdorffness is equivalent to triviality of the
specialization relation. -/
@[stacks 0905 "Hausdorff iff specialization is trivial"]
theorem t2Space_iff_specializes_imp_eq (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ ∀ ⦃x y : X⦄, x ⤳ y → x = y := sorry

/-- For a spectral space, Hausdorffness is equivalent to every singleton
being closed. -/
@[stacks 0905 "Hausdorff iff points are closed"]
theorem t2Space_iff_isClosed_singleton (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ ∀ x : X, IsClosed ({x} : Set X) := sorry

/-- For a spectral space, Hausdorffness is equivalent to each point being the
generic point of its irreducible component. -/
@[stacks 0905 "Hausdorff iff irreducible-component points are generic"]
theorem t2Space_iff_isGenericPoint_irreducibleComponent (X : Type u)
    [TopologicalSpace X] [SpectralSpace X] :
    T2Space X ↔ ∀ x : X, IsGenericPoint x (irreducibleComponent x) := sorry

/-- For a spectral space, Hausdorffness is equivalent to the constructible
topology agreeing with the original topology. -/
@[stacks 0905 "Hausdorff iff patch topology is original"]
theorem t2Space_iff_constructibleTopology_eq (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ constructibleTopology X = ‹TopologicalSpace X› := sorry

/-- Lemma 5.23.8: the standard profinite, separation, specialization, and
constructible-topology criteria for a spectral space are equivalent. -/
@[stacks 0905]
theorem profinite_criteria (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P),
        T2Space X,
        TotallyDisconnectedSpace X,
        ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U,
        ∀ ⦃x y : X⦄, x ⤳ y → x = y,
        ∀ x : X, IsClosed ({x} : Set X),
        ∀ x : X, IsGenericPoint x (irreducibleComponent x),
        constructibleTopology X = ‹TopologicalSpace X› ] := sorry

end SpectralSpace

-- Public smoke checks keep the reusable criteria discoverable from this leaf.
