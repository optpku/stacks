module

public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Indexed Filtrations

A decreasing filtration on an object `A` in a category `C`, indexed by a preordered type `I`,
is a monotone map `Iᵒᵈ →o Subobject A` — equivalently an antitone family of subobjects of `A`.

The standard case is `I = ℤ`, giving `DecreasingFiltration A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A decreasing filtration on an object `A`, indexed by a preordered type `I`.
Concretely this is an antitone family `I → Subobject A`, bundled as a monotone map from `Iᵒᵈ`. -/
abbrev IndexedFiltration (I : Type*) [Preorder I] {C : Type u} [Category.{v} C] (A : C) :=
  Iᵒᵈ →o Subobject A

/-- The standard `ℤ`-indexed decreasing filtration. -/
abbrev DecreasingFiltration {C : Type u} [Category.{v} C] (A : C) := IndexedFiltration ℤ A

namespace IndexedFiltration

variable {I : Type*} [Preorder I] {A : C}

/-- The `i`-th stage of the filtration, as a subobject. -/
abbrev stage (F : IndexedFiltration I A) (i : I) : Subobject A :=
  F (OrderDual.toDual i)

/-- The stages form an antitone family. -/
theorem antitone (F : IndexedFiltration I A) : Antitone F.stage :=
  fun _ _ hij ↦ F.monotone (OrderDual.toDual_le_toDual.mpr hij)

/-- If `i ≤ j` then `F.stage j ≤ F.stage i`. -/
theorem stage_mono (F : IndexedFiltration I A) {i j : I} (hij : i ≤ j) :
    F.stage j ≤ F.stage i :=
  F.antitone hij

/-- The canonical inclusion morphism `F^j A ⟶ F^i A` for `i ≤ j`. -/
noncomputable abbrev inclusion (F : IndexedFiltration I A) {i j : I} (hij : i ≤ j) :
    (F.stage j : C) ⟶ (F.stage i : C) :=
  Subobject.ofLE _ _ (F.stage_mono hij)

/-- Composing a stage inclusion with its subobject arrow gives the arrow of the smaller stage. -/
@[simp]
theorem inclusion_arrow (F : IndexedFiltration I A) {i j : I} (hij : i ≤ j) :
    F.inclusion hij ≫ (F.stage i).arrow = (F.stage j).arrow :=
  Subobject.ofLE_arrow (F.stage_mono hij)

/-- The inclusion from a stage to itself is the identity. -/
@[simp]
theorem inclusion_refl (F : IndexedFiltration I A) (i : I) :
    F.inclusion (le_refl i) = 𝟙 _ := by
  apply (cancel_mono (F.stage i).arrow).1
  simp

/-- Inclusions compose transitively. -/
theorem inclusion_trans (F : IndexedFiltration I A) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    F.inclusion hjk ≫ F.inclusion hij = F.inclusion (hij.trans hjk) := by
  apply (cancel_mono (F.stage i).arrow).1
  simp

end IndexedFiltration

namespace DecreasingFiltration

variable {A : C}

/-- Consecutive stages satisfy `F.stage (p + 1) ≤ F.stage p`. -/
theorem succ_le (F : DecreasingFiltration A) (p : ℤ) :
    F.stage (p + 1) ≤ F.stage p :=
  F.antitone (by omega : p ≤ p + 1)

/-- The canonical inclusion `F.succInclusion p` from the next stage to the current stage. -/
noncomputable abbrev succInclusion (F : DecreasingFiltration A) (p : ℤ) :
    (F.stage (p + 1) : C) ⟶ (F.stage p : C) :=
  F.inclusion (show p ≤ p + 1 by omega)

/-- Composing a consecutive-stage inclusion with the current stage arrow gives the next arrow. -/
@[simp]
theorem succInclusion_arrow (F : DecreasingFiltration A) (p : ℤ) :
    F.succInclusion p ≫ (F.stage p).arrow = (F.stage (p + 1)).arrow :=
  F.inclusion_arrow (show p ≤ p + 1 by omega)

end DecreasingFiltration

end CategoryTheory
