module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sierpinski Space

The canonical Sierpinski space, represented by `Prop` with its Mathlib topology,
and its irreducible-closed and Krull-dimension API.
-/

@[expose] public section

open Set TopologicalSpace Order

namespace Sierpinski

/-- Example 5.10.4: the opens of the Sierpinski space are empty, `{True}`, and the whole space. -/
@[stacks 0057 "the three open subsets of the Sierpinski space"]
theorem isOpen_iff (s : Set Prop) :
    IsOpen s ↔ s = ∅ ∨ s = {True} ∨ s = univ := by
  rw [Topology.IsUpperSet.isOpen_iff_isUpperSet]
  constructor
  · intro hs
    by_cases hFalse : False ∈ s
    · right
      right
      exact eq_univ_of_forall fun p ↦ hs (False.elim) hFalse
    · by_cases hTrue : True ∈ s
      · right
        left
        ext p
        constructor
        · intro hp
          by_cases hp' : p
          · exact eq_true_intro hp'
          · exact (hFalse (eq_false_intro hp' ▸ hp)).elim
        · intro hp
          exact hp ▸ hTrue
      · left
        exact Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ by
          by_cases hp' : p
          · exact hTrue (eq_true_intro hp' ▸ hp)
          · exact hFalse (eq_false_intro hp' ▸ hp)
  · rintro (rfl | rfl | rfl)
    · exact isUpperSet_empty
    · simpa using isUpperSet_Ici (α := Prop) True
    · exact isUpperSet_univ

/-- The irreducible closed subset of the Sierpinski space carried by its closed point. -/
@[stacks 0057 "the closed-point irreducible closed subset of the Sierpinski space"]
def closedPoint : IrreducibleCloseds Prop :=
  ⟨closure {False}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- The irreducible closed subset of the Sierpinski space carried by the whole space. -/
@[stacks 0057 "the whole-space irreducible closed subset of the Sierpinski space"]
def whole : IrreducibleCloseds Prop :=
  ⟨closure {True}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- The carrier of the closed-point irreducible closed subset is `{False}`. -/
@[simp]
theorem coe_closedPoint : (closedPoint : Set Prop) = {False} := by
  simp [closedPoint]

/-- The carrier of the whole-space irreducible closed subset is `univ`. -/
@[simp]
theorem coe_whole : (whole : Set Prop) = univ := by
  simp [whole]

private theorem eq_closedPoint_or_eq_whole (Z : IrreducibleCloseds Prop) :
    Z = closedPoint ∨ Z = whole := by
  rcases (isOpen_iff ((Z : Set Prop)ᶜ)).mp Z.isClosed.isOpen_compl with h | h | h
  · right
    apply IrreducibleCloseds.ext
    rw [coe_whole]
    apply compl_injective
    simpa using h
  · left
    apply IrreducibleCloseds.ext
    rw [coe_closedPoint]
    apply compl_injective
    simpa using h
  · have hZ : (Z : Set Prop) = ∅ := by
      apply compl_injective
      simpa using h
    exact (Z.isIrreducible.nonempty.ne_empty hZ).elim

private theorem closedPoint_le_whole : closedPoint ≤ whole := by
  change (closedPoint : Set Prop) ⊆ (whole : Set Prop)
  rw [coe_closedPoint, coe_whole]
  exact subset_univ _

private theorem not_whole_le_closedPoint : ¬whole ≤ closedPoint := by
  intro h
  have h' : (whole : Set Prop) ⊆ (closedPoint : Set Prop) := h
  rw [coe_whole, coe_closedPoint] at h'
  simpa using h' (mem_univ True)

/-- Example 5.10.4: the closed point followed by the whole space is a maximal chain of
irreducible closed subsets. -/
@[stacks 0057 "the maximal chain from the closed point to the whole space"]
theorem irreducibleCloseds_isMaxChain :
    IsMaxChain (· ≤ ·) ({closedPoint, whole} : Set (IrreducibleCloseds Prop)) := by
  constructor
  · rintro Z hZ W hW hne
    simp only [mem_insert_iff, mem_singleton_iff] at hZ hW
    rcases hZ with rfl | rfl
    · rcases hW with rfl | rfl
      · exact (hne rfl).elim
      · exact Or.inl closedPoint_le_whole
    · rcases hW with rfl | rfl
      · exact Or.inr closedPoint_le_whole
      · exact (hne rfl).elim
  · intro t _ ht
    apply Set.Subset.antisymm ht
    intro Z _
    rcases eq_closedPoint_or_eq_whole Z with rfl | rfl <;> simp

/-- Example 5.10.4: the Sierpinski space has topological Krull dimension one. -/
@[stacks 0057 "the Sierpinski space has Krull dimension one"]
theorem topologicalKrullDim_eq_one : topologicalKrullDim Prop = 1 := by
  unfold topologicalKrullDim
  apply le_antisymm
  · rw [Order.krullDim_le_one_iff]
    intro Z
    rcases eq_closedPoint_or_eq_whole Z with rfl | rfl
    · left
      intro Y _
      rcases eq_closedPoint_or_eq_whole Y with rfl | rfl
      · exact le_rfl
      · exact closedPoint_le_whole
    · right
      intro Y _
      rcases eq_closedPoint_or_eq_whole Y with rfl | rfl
      · exact closedPoint_le_whole
      · exact le_rfl
  · rw [Order.one_le_krullDim_iff]
    exact ⟨closedPoint, whole,
      closedPoint_le_whole.lt_of_not_ge not_whole_le_closedPoint⟩

end Sierpinski
