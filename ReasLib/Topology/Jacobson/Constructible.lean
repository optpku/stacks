module

public import Mathlib.Topology.Constructible
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Jacobson.ClosedPoints

/-!
# Constructible Closed-Point Traces

Constructible subsets of a Jacobson space are recovered from their traces on
the canonical subtype of closed points.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation TopologicalSpace

namespace JacobsonSpace.ClosedPoints

variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

/-- Lemma 5.18.8 (1): taking the trace on `closedPoints X` is a bijection on
constructible subsets. -/
@[stacks 005Y "constructible closed-point trace correspondence"]
theorem constructible_bijOn :
    Set.BijOn
      (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F} := sorry

/-- The closed-point trace equivalence induced by a supplied constructible trace bijection. The
inverse is noncomputable; use `constructibleTraceEquiv_symm_apply_trace` rather than inspecting
its choice. Keeping the bijection proof as an argument ensures that this non-Prop construction
does not inherit statement-stage proof debt. -/
@[stacks 005Y "equivalence of constructible closed-point traces"]
noncomputable def constructibleTraceEquiv
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F}) :
    {E : Set X // IsConstructible E} ≃
      {F : Set (closedPoints X) // IsConstructible F} :=
  h.equiv _

/-- `constructibleTraceEquiv` applies to a constructible subset by taking its
canonical trace on `closedPoints X`. -/
@[simp]
theorem constructibleTraceEquiv_apply
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F})
    (E : {E : Set X // IsConstructible E}) :
    (constructibleTraceEquiv h E).val = (closedPoints X) ↓∩ E.val := sorry

/-- Membership in the forward image under `constructibleTraceEquiv` is
membership of the underlying closed point in the ambient subset. -/
@[simp]
theorem mem_constructibleTraceEquiv_iff
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F})
    (E : {E : Set X // IsConstructible E}) {x : closedPoints X} :
    x ∈ (constructibleTraceEquiv h E).val ↔ x.val ∈ E.val := sorry

/-- The chosen inverse of `constructibleTraceEquiv` is characterized by its
closed-point trace. -/
@[simp]
theorem constructibleTraceEquiv_symm_apply_trace
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F})
    (F : {F : Set (closedPoints X) // IsConstructible F}) :
    (closedPoints X) ↓∩ ((constructibleTraceEquiv h).symm F).val = F.val := sorry

end JacobsonSpace.ClosedPoints

namespace Topology.IsConstructible

variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

/-- Constructible closed-point traces reflect and preserve inclusion. -/
theorem closedPointsTrace_subset_iff
    {E E' : Set X} (hE : IsConstructible E) (hE' : IsConstructible E') :
    (closedPoints X) ↓∩ E ⊆ (closedPoints X) ↓∩ E' ↔ E ⊆ E' := sorry

/-- A constructible subset has constructible trace on the closed-point subtype. -/
theorem closedPointsTrace {E : Set X} (hE : IsConstructible E) :
    IsConstructible ((closedPoints X) ↓∩ E) := sorry

/-- Lemma 5.18.8 (2): for a constructible subset, being open and retrocompact
is reflected and preserved by its closed-point trace. -/
@[stacks 005Y "preservation of open retrocompact subsets"]
theorem isOpen_and_isRetrocompact_iff_closedPointsTrace
    {E : Set X} (hE : IsConstructible E) :
    IsOpen E ∧ IsRetrocompact E ↔
      IsOpen ((closedPoints X) ↓∩ E) ∧ IsRetrocompact ((closedPoints X) ↓∩ E) := sorry

/-- Lemma 5.18.8 (3): for a constructible subset, being the complement of an
open retrocompact subset is reflected and preserved by its closed-point trace. -/
@[stacks 005Y "preservation of complements of open retrocompact subsets"]
theorem isOpen_compl_and_isRetrocompact_compl_iff_closedPointsTrace
    {E : Set X} (hE : IsConstructible E) :
    IsOpen Eᶜ ∧ IsRetrocompact Eᶜ ↔
      IsOpen ((closedPoints X) ↓∩ E)ᶜ ∧ IsRetrocompact ((closedPoints X) ↓∩ E)ᶜ := sorry

end Topology.IsConstructible
