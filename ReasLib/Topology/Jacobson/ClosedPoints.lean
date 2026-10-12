/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.Topology.LocallyClosed.FiniteUnion

/-!
# Closed-Point Traces in Jacobson Spaces

The closed-point subtype is Mathlib's canonical `closedPoints X`.  This leaf
adds the finite-locally-closed trace correspondence that it satisfies in a
Jacobson space.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.IsOpenCover

/-- Lemma 5.18.4 (2): in a Jacobson space, the closed points are the union of
the closed points of the members of any open cover, viewed in the ambient space. -/
@[stacks 005W "closed points are the union of those in the cover members"]
theorem closedPoints_eq_iUnion_image {ι : Type*} {U : ι → Opens X} [JacobsonSpace X]
    (hU : IsOpenCover U) :
    closedPoints X = ⋃ i, Subtype.val '' closedPoints (U i) := sorry

end TopologicalSpace.IsOpenCover

namespace JacobsonSpace.ClosedPoints

variable [JacobsonSpace X]

/-- Lemma 5.18.7 (1): taking the trace on `closedPoints X` is a bijection on
finite unions of locally closed subsets. -/
@[stacks 005Z "bijection on finite unions of locally closed subsets"]
theorem finiteUnionOfLocallyClosed_bijOn :
    Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F} := sorry

/-- The closed-point trace equivalence induced by a supplied finite-locally-closed trace
bijection. The inverse is noncomputable; use `finiteUnionTraceEquiv_symm_apply_trace` rather
than inspecting its choice. Keeping the bijection proof as an argument ensures that this
non-Prop construction does not inherit statement-stage proof debt. -/
@[stacks 005Z "equivalence of finite-locally-closed closed-point traces"]
noncomputable def finiteUnionTraceEquiv
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F}) :
    {E : Set X // IsFiniteUnionOfLocallyClosed E} ≃
      {F : Set (closedPoints X) // IsFiniteUnionOfLocallyClosed F} :=
  h.equiv _

/-- `finiteUnionTraceEquiv` applies to a finite-locally-closed subset by
taking its canonical trace on `closedPoints X`. -/
@[simp]
theorem finiteUnionTraceEquiv_apply
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F})
    (E : {E : Set X // IsFiniteUnionOfLocallyClosed E}) :
    (finiteUnionTraceEquiv h E).val = (closedPoints X) ↓∩ E.val := sorry

/-- Membership in the forward image under `finiteUnionTraceEquiv` is
membership of the underlying closed point in the ambient subset. -/
@[simp]
theorem mem_finiteUnionTraceEquiv_iff
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F})
    (E : {E : Set X // IsFiniteUnionOfLocallyClosed E}) {x : closedPoints X} :
    x ∈ (finiteUnionTraceEquiv h E).val ↔ x.val ∈ E.val := sorry

/-- The chosen inverse of `finiteUnionTraceEquiv` is characterized by its
closed-point trace. -/
@[simp]
theorem finiteUnionTraceEquiv_symm_apply_trace
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F})
    (F : {F : Set (closedPoints X) // IsFiniteUnionOfLocallyClosed F}) :
    (closedPoints X) ↓∩ ((finiteUnionTraceEquiv h).symm F).val = F.val := sorry

end JacobsonSpace.ClosedPoints

namespace IsFiniteUnionOfLocallyClosed

variable [JacobsonSpace X]

/-- Lemma 5.18.7 (2): the closed-point trace reflects and preserves inclusion
between finite unions of locally closed subsets. -/
@[stacks 005Z "inclusion-preserving correspondence"]
theorem closedPointsTrace_subset_iff
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E') :
    (closedPoints X) ↓∩ E ⊆ (closedPoints X) ↓∩ E' ↔ E ⊆ E' := sorry

/-- Lemma 5.18.7 (3): within the finite-locally-closed trace correspondence,
local closedness is reflected and preserved. -/
@[stacks 005Z "preservation of locally closed subsets"]
theorem isLocallyClosed_iff_closedPointsTrace
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsLocallyClosed E ↔ IsLocallyClosed ((closedPoints X) ↓∩ E) := sorry

/-- Lemma 5.18.7 (4): within the finite-locally-closed trace correspondence,
openness is reflected and preserved. -/
@[stacks 005Z "preservation of open subsets"]
theorem isOpen_iff_closedPointsTrace
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsOpen E ↔ IsOpen ((closedPoints X) ↓∩ E) := sorry

/-- Lemma 5.18.7 (5): within the finite-locally-closed trace correspondence,
closedness is reflected and preserved. -/
@[stacks 005Z "preservation of closed subsets"]
theorem isClosed_iff_closedPointsTrace
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsClosed E ↔ IsClosed ((closedPoints X) ↓∩ E) := sorry

end IsFiniteUnionOfLocallyClosed
