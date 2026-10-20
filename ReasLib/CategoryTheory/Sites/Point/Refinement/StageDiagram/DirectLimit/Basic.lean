module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.Basic
public import ReasLib.Order.DirectLimit

/-!
# Direct-limit indices for refinement-stage diagrams

This file constructs the ordered direct limit of the stage indices and exposes its canonical
inclusions and comparison API.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v d r

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace DirectedPreorderSystem.StageDiagram

variable {δ : Type d} [Preorder δ]
variable (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)

/-- The stage-index transition maps form Mathlib's canonical directed system. -/
instance index_directed_system
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) :
    DirectedSystem (fun a => (D.obj a).index)
      (fun a b hab => D.index_map (a := a) (b := b) hab) where
  map_self := DirectedPreorderSystem.StageDiagram.index_map_refl D
  map_map := fun _ _ _ hij hjk i =>
    DirectedPreorderSystem.StageDiagram.index_map_comp D hij hjk i

variable [IsDirectedOrder δ]

/-- The ordered direct limit of the stage indices.  Its carrier is Mathlib's `DirectLimit`; the
order and canonical inclusions are supplied by `ReasLib.Order.DirectLimit`. -/
noncomputable def index_preord : Preord :=
  _root_.DirectLimit.preord
    (fun a b hab => D.index_map (a := a) (b := b) hab)

/-- The canonical order embedding of a stage index into the directed-limit index. -/
def index_inclusion (a : δ) : (D.obj a).index ↪o D.index_preord :=
  _root_.DirectLimit.inclusion
    (fun i j hij => D.index_map (a := i) (b := j) hij) a

/-- The underlying value of a stage inclusion is Mathlib's direct-limit representative. -/
@[simp] theorem index_inclusion_apply (a : δ) (i : (D.obj a).index) :
    D.index_inclusion a i =
      (⟦⟨a, i⟩⟧ : _root_.DirectLimit (fun a : δ => (D.obj a).index)
        (fun a b hab => D.index_map (a := a) (b := b) hab)) := rfl

/-- Directed-limit index inclusions are natural with respect to diagram transitions. -/
theorem index_inclusion_natural {a b : δ} (hab : a ≤ b) (i : (D.obj a).index) :
    D.index_inclusion a i = D.index_inclusion b (D.index_map hab i) := sorry

/-- The canonical index inclusions compose strictly along the diagram. -/
theorem index_inclusion_comp {a b : δ} (hab : a ≤ b) :
    (D.index_map hab).comp (D.index_inclusion b) = D.index_inclusion a := sorry

/-- A stage inclusion preserves and reflects the order of that stage. -/
theorem index_inclusion_le_iff {a : δ} {i j : (D.obj a).index} :
    D.index_inclusion a i ≤ D.index_inclusion a j ↔ i ≤ j := sorry

/-- Comparisons between indices from two stages are witnessed after a common diagram transition. -/
theorem index_le_iff {a b : δ}
    (i : (D.obj a).index) (j : (D.obj b).index) :
    D.index_inclusion a i ≤ D.index_inclusion b j ↔
      ∃ c, ∃ hac : a ≤ c, ∃ hbc : b ≤ c,
        D.index_map hac i ≤ D.index_map hbc j := sorry

/-- Equality of two stage inclusions is equality after moving to one common diagram stage. -/
theorem index_eq_iff {a b : δ}
    (i : (D.obj a).index) (j : (D.obj b).index) :
    D.index_inclusion a i = D.index_inclusion b j ↔
      ∃ c, ∃ hac : a ≤ c, ∃ hbc : b ≤ c,
        D.index_map hac i = D.index_map hbc j := sorry

/-- Every directed-limit index is represented by an index from some diagram stage. -/
theorem exists_eq_index_inclusion (x : D.index_preord) :
    ∃ a i, x = D.index_inclusion a i := sorry

/-- The directed-limit index is directed. -/
theorem index_preord_directed : IsDirectedOrder D.index_preord := sorry

/-- Typeclass access to directedness of the directed-limit index. -/
noncomputable instance index_preord_is_directed : IsDirectedOrder D.index_preord :=
  D.index_preord_directed

end DirectedPreorderSystem.StageDiagram

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
