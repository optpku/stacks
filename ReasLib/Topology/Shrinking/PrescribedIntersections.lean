module

public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Shrinking.Controlled

/-!
# Compact-subset shrinkings with prescribed intersections

This leaf owns the local compact Hausdorff shrinking statement whose output
controls a fixed finite tuple of members of an open family.
-/

@[expose] public section

open Set TopologicalSpace

universe u v

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- A shrinking of an open family whose closures remain in the ambient opens and whose finite
tuple intersections lie in prescribed opens along a subset. -/
@[stacks 09UX "prescribed-intersection shrinking predicate"]
structure IsOpenShrinkingWithPrescribedIntersections
    (Z : Set X) (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) : Prop extends IsTuplewiseOpenCover Z p W V where
  /-- The closure of each shrunken open lies in its ambient open. -/
  closure_subset (i : I) : closure (V i : Set X) ⊆ U i

/-- The cover, closure-control, and tuplewise-containment conditions defining a prescribed
intersection shrinking. -/
@[stacks 09UX]
theorem isOpenShrinkingWithPrescribedIntersections_iff
    (Z : Set X) (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) :
    IsOpenShrinkingWithPrescribedIntersections Z p U W V ↔
      Z ⊆ ⋃ i, (V i : Set X) ∧
        (∀ i, closure (V i : Set X) ⊆ U i) ∧
          ∀ σ : Fin (p + 1) → I, (⋂ j, (V (σ j) : Set X)) ⊆ W σ := sorry

namespace IsOpenShrinkingWithPrescribedIntersections

/-- Every prescribed-intersection shrinking is subordinate to its ambient open family. -/
theorem subset {Z : Set X} {p : ℕ} {U : I → Opens X}
    {W : (Fin (p + 1) → I) → Opens X} {V : I → Opens X}
    (R : IsOpenShrinkingWithPrescribedIntersections Z p U W V) (i : I) :
    (V i : Set X) ⊆ U i := sorry

/-- The relative closure of a prescribed-intersection shrinking remains in its ambient member. -/
theorem closure_inter_subset {Z : Set X} {p : ℕ} {U : I → Opens X}
    {W : (Fin (p + 1) → I) → Opens X} {V : I → Opens X}
    (R : IsOpenShrinkingWithPrescribedIntersections Z p U W V) (i : I) :
    closure (V i : Set X) ∩ Z ⊆ U i := sorry

end IsOpenShrinkingWithPrescribedIntersections

end TopologicalSpace

namespace IsCompact

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- Stacks Lemma 5.13.6 (`09UX`): a compact subset of a locally compact Hausdorff space admits
a shrinking with prescribed finite tuple intersections. -/
@[stacks 09UX]
theorem exists_open_shrinking_with_prescribed_intersections
    [LocallyCompactSpace X] [T2Space X]
    {Z : Set X} (hZ : IsCompact Z) (p : ℕ) (U : I → Opens X)
    (W : (Fin (p + 1) → I) → Opens X) (hcover : Z ⊆ ⋃ i, (U i : Set X))
    (hW_subset : ∀ σ : Fin (p + 1) → I, (W σ : Set X) ⊆ ⋂ j, (U (σ j) : Set X))
    (hW_on_Z : ∀ σ : Fin (p + 1) → I,
      (W σ : Set X) ∩ Z = (⋂ j, (U (σ j) : Set X)) ∩ Z) :
    ∃ V : I → Opens X,
      TopologicalSpace.IsOpenShrinkingWithPrescribedIntersections Z p U W V := sorry

end IsCompact
