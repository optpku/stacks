module

public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Shrinking.Controlled

/-!
# Relative tuplewise shrinkings

This leaf owns the compact-subset shrinking API with relative closure control
under pairwise separation of points of the compact subset.
-/

@[expose] public section

open Set TopologicalSpace

universe u v

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- A shrinking of an open family with ambient containment, relative closure control, and
prescribed finite tuple intersections along a compact subset. -/
@[stacks 0CY5 "relative tuple-intersection shrinking predicate"]
structure IsRelativeTuplewiseShrinking
    (Z : Set X) (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) : Prop extends IsTuplewiseOpenCover Z p W V where
  /-- Each shrunken open lies in the corresponding ambient open. -/
  subset (i : I) : (V i : Set X) ⊆ U i
  /-- The closure of each shrunken open meets the compact subset inside its ambient open. -/
  closure_inter_subset (i : I) : closure (V i : Set X) ∩ Z ⊆ U i

/-- The cover, ambient-containment, relative-closure, and tuplewise-containment conditions
defining a tuple-intersection shrinking. -/
@[stacks 0CY5]
theorem isRelativeTuplewiseShrinking_iff
    (Z : Set X) (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) :
    IsRelativeTuplewiseShrinking Z p U W V ↔
      Z ⊆ ⋃ i, (V i : Set X) ∧
        (∀ i, (V i : Set X) ⊆ U i) ∧
          (∀ i, closure (V i : Set X) ∩ Z ⊆ U i) ∧
            ∀ σ : Fin (p + 1) → I, (⋂ j, (V (σ j) : Set X)) ⊆ W σ := sorry

end TopologicalSpace

namespace IsCompact

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- Stacks Lemma 5.13.7 (`0CY5`): a compact subset whose distinct points have separated ambient
neighborhoods admits a tuple-intersection shrinking. -/
@[stacks 0CY5]
theorem exists_relative_tuplewise_shrinking
    {Z : Set X} (hZ : IsCompact Z)
    (hZsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      SeparatedNhds ({x} : Set X) ({y} : Set X))
    (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (hcover : Z ⊆ ⋃ i, (U i : Set X))
    (hW_subset : ∀ σ : Fin (p + 1) → I, (W σ : Set X) ⊆ ⋂ j, (U (σ j) : Set X))
    (hW_on_Z : ∀ σ : Fin (p + 1) → I,
      (W σ : Set X) ∩ Z = (⋂ j, (U (σ j) : Set X)) ∩ Z) :
    ∃ V : I → Opens X, TopologicalSpace.IsRelativeTuplewiseShrinking Z p U W V := sorry

end IsCompact
