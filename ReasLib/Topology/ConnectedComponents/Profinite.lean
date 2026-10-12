/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Category.Profinite.Recognition
public import ReasLib.Topology.ConnectedComponents.Clopen

/-!
# Profinite Connected-Component Quotients

This module records conditions under which the canonical quotient
`ConnectedComponents X` is Hausdorff, hence admits Mathlib's bundled
profinite-space structure.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

namespace ConnectedComponents

/-- The clopen-neighborhood description of every connected component makes the
connected-components quotient Hausdorff. -/
@[stacks 0900 "Hausdorff connected-components quotient"]
theorem t2Space_of_connectedComponent_eq_iInter_isClopen [CompactSpace X]
    (hcomponents :
      ∀ x : X,
        connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z) :
    T2Space (ConnectedComponents X) := sorry

/-- A compact space whose connected components have the clopen-neighborhood
description admits a profinite connected-components quotient. -/
theorem exists_profinite_of_connectedComponent_eq_iInter_isClopen [CompactSpace X]
    (hcomponents :
      ∀ x : X,
        connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z) :
    ∃ P : Profinite.{u}, Nonempty (ConnectedComponents X ≃ₜ P) := sorry

/-- Connected components of a spectral space form a Hausdorff quotient. -/
@[stacks 0906 "Hausdorff quotient of a spectral space"]
instance t2Space_of_spectralSpace [SpectralSpace X] :
    T2Space (ConnectedComponents X) := sorry

/-- Connected components of a spectral space admit a profinite model. -/
theorem exists_profinite_of_spectralSpace [SpectralSpace X] :
    ∃ P : Profinite.{u}, Nonempty (ConnectedComponents X ≃ₜ P) := sorry

end ConnectedComponents
