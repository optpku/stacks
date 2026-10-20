/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.SmallObject.SuccStruct.Bounded

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The closed initial segment used for an iteration with prescribed top index `j`. -/
abbrev Shape (j : J) := Set.Iic j

/-- An index `i ≤ j`, regarded as an object of the bounded iteration shape at `j`. -/
abbrev index {i j : J} (h : i ≤ j) : Shape j := ⟨i, h⟩

/-- The iteration diagram of a successor structure, restricted to the closed initial segment
ending at `j`. -/
noncomputable abbrev diagram (Φ : SuccStruct C) (j : J)
    [HasIterationOfShape (Shape j) C] : Shape j ⥤ C :=
  Φ.iterationFunctor (Shape j)

/-- The object at `i ≤ j` in the bounded iteration ending at `j`. -/
noncomputable abbrev obj (Φ : SuccStruct C) {i j : J} (h : i ≤ j)
    [HasIterationOfShape (Shape j) C] : C :=
  (diagram Φ j).obj (index h)

/-- The canonical map between two stages of the same bounded iteration. -/
noncomputable def map (Φ : SuccStruct C) {i₁ i₂ j : J}
    (h₁ : i₁ ≤ j) (h₂ : i₂ ≤ j) (h₁₂ : i₁ ≤ i₂)
    [HasIterationOfShape (Shape j) C] : obj Φ h₁ ⟶ obj Φ h₂ :=
  (diagram Φ j).map (homOfLE h₁₂)

/-- The top object of the bounded iteration ending at `j`. -/
noncomputable abbrev top (Φ : SuccStruct C) (j : J)
    [HasIterationOfShape (Shape j) C] : C :=
  obj Φ (le_rfl : j ≤ j)

/-- The canonical map from a stage to the top of the same bounded iteration. -/
noncomputable def toTop (Φ : SuccStruct C) {i j : J} (h : i ≤ j)
    [HasIterationOfShape (Shape j) C] : obj Φ h ⟶ top Φ j :=
  map Φ h le_rfl h

/-- The predecessor index in the bounded iteration ending at `Order.succ i`. -/
abbrev predIndex (i : J) : Shape (Order.succ i) :=
  index (Order.le_succ i)

/-- The successor of the predecessor index inside the bounded iteration ending at
`Order.succ i`. -/
noncomputable abbrev succIndex (i : J) : Shape (Order.succ i) :=
  Order.succ (predIndex i)

/-- The predecessor index is not maximal in the bounded shape ending at its successor. -/
@[stacks 01DM "predecessor index below the bounded top"]
theorem not_isMax_predIndex [NoMaxOrder J] (i : J) :
    ¬ IsMax (predIndex i) := sorry

/-- The predecessor object in the bounded iteration ending at `Order.succ i`. -/
noncomputable abbrev pred (Φ : SuccStruct C) (i : J)
    [HasIterationOfShape (Shape (Order.succ i)) C] : C :=
  (diagram Φ (Order.succ i)).obj (predIndex i)

/-- The object immediately after the predecessor in the bounded iteration ending at
`Order.succ i`. -/
noncomputable abbrev succ (Φ : SuccStruct C) (i : J)
    [HasIterationOfShape (Shape (Order.succ i)) C] : C :=
  (diagram Φ (Order.succ i)).obj (succIndex i)

/-- The canonical identification of the next bounded stage with the successor construction
applied to its predecessor. -/
@[stacks 01DM]
noncomputable def succIso [NoMaxOrder J] (Φ : SuccStruct C) (i : J)
    [HasIterationOfShape (Shape (Order.succ i)) C] :
    succ Φ i ≅ Φ.succ (pred Φ i) :=
  Φ.iterationFunctorObjSuccIso (predIndex i)
    (not_isMax_predIndex i)

/-- The canonical successor map inside the bounded iteration. -/
@[stacks 01DM]
noncomputable def toSucc [NoMaxOrder J] (Φ : SuccStruct C) (i : J)
    [HasIterationOfShape (Shape (Order.succ i)) C] :
    pred Φ i ⟶ succ Φ i :=
  Φ.toSucc (pred Φ i) ≫ (succIso Φ i).inv

/-- Identity law for maps inside a bounded iteration. -/
@[simp]
theorem map_id (Φ : SuccStruct C) {i j : J} (h : i ≤ j)
    [HasIterationOfShape (Shape j) C] :
    map Φ h h le_rfl = 𝟙 (obj Φ h) := sorry

/-- Composition law for maps inside a bounded iteration. -/
theorem map_comp (Φ : SuccStruct C) {i₁ i₂ i₃ j : J}
    (h₁ : i₁ ≤ j) (h₂ : i₂ ≤ j) (h₃ : i₃ ≤ j)
    (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    [HasIterationOfShape (Shape j) C] :
    map Φ h₁ h₃ (h₁₂.trans h₂₃) = map Φ h₁ h₂ h₁₂ ≫ map Φ h₂ h₃ h₂₃ := sorry

end CategoryTheory.SmallObject.SuccStruct.Bounded

namespace CategoryTheory.SmallObject.SuccStruct.OrdinalBounded

variable {C : Type u} [Category.{v} C]

/-- The universe-preserving well-order representing the closed ordinal interval `[0, β]`. -/
abbrev Shape (β : Ordinal.{w}) := (Order.succ β).ToType

/-- The closed ordinal interval `[0, β]` is nonempty. -/
noncomputable instance shapeOrderBot (β : Ordinal.{w}) : OrderBot (Shape β) :=
  WellFoundedLT.toOrderBot _

/-- An ordinal `α ≤ β`, regarded as an index in the closed interval `[0, β]`. -/
noncomputable abbrev index {α β : Ordinal.{w}} (h : α ≤ β) : Shape β :=
  Ordinal.ToType.mk ⟨α, Order.lt_succ_iff.2 h⟩

/-- The closed-interval index construction is monotone in its ordinal argument. -/
@[stacks 01DM "monotonicity of bounded ordinal indices"]
theorem index_mono {α₁ α₂ β : Ordinal.{w}} (h₁ : α₁ ≤ β) (h₂ : α₂ ≤ β)
    (h₁₂ : α₁ ≤ α₂) : index h₁ ≤ index h₂ := sorry

/-- The iteration diagram of a successor structure on the universe-preserving closed interval
`[0, β]`. -/
noncomputable abbrev diagram (Φ : SuccStruct C) (β : Ordinal.{w})
    [HasIterationOfShape (Shape β) C] : Shape β ⥤ C :=
  Φ.iterationFunctor (Shape β)

/-- The object at `α ≤ β` in the ordinal-bounded iteration ending at `β`. -/
noncomputable abbrev obj (Φ : SuccStruct C) {α β : Ordinal.{w}} (h : α ≤ β)
    [HasIterationOfShape (Shape β) C] : C :=
  (diagram Φ β).obj (index h)

/-- The canonical map between two stages of the same ordinal-bounded iteration. -/
noncomputable def map (Φ : SuccStruct C) {α₁ α₂ β : Ordinal.{w}}
    (h₁ : α₁ ≤ β) (h₂ : α₂ ≤ β) (h₁₂ : α₁ ≤ α₂)
    [HasIterationOfShape (Shape β) C] : obj Φ h₁ ⟶ obj Φ h₂ :=
  (diagram Φ β).map (homOfLE (index_mono h₁ h₂ h₁₂))

/-- The top object of the ordinal-bounded iteration ending at `β`. -/
noncomputable abbrev top (Φ : SuccStruct C) (β : Ordinal.{w})
    [HasIterationOfShape (Shape β) C] : C :=
  obj Φ (le_rfl : β ≤ β)

/-- The canonical map from a stage to the top of the same ordinal-bounded iteration. -/
noncomputable def toTop (Φ : SuccStruct C) {α β : Ordinal.{w}} (h : α ≤ β)
    [HasIterationOfShape (Shape β) C] : obj Φ h ⟶ top Φ β :=
  map Φ h le_rfl h

/-- The index of `α` in the ordinal-bounded iteration ending at `α + 1`. -/
noncomputable abbrev predIndex (α : Ordinal.{w}) : Shape (Order.succ α) :=
  index (Order.le_succ α)

/-- The successor of the index of `α` in the ordinal-bounded iteration ending at `α + 1`. -/
noncomputable abbrev succIndex (α : Ordinal.{w}) : Shape (Order.succ α) :=
  Order.succ (predIndex α)

/-- The `α`-index is not maximal in the ordinal-bounded shape ending at `α + 1`. -/
@[stacks 01DM "ordinal predecessor index below the bounded top"]
theorem not_isMax_predIndex (α : Ordinal.{w}) :
    ¬ IsMax (predIndex α) := sorry

/-- The `α`-stage in the ordinal-bounded iteration ending at `α + 1`. -/
noncomputable abbrev pred (Φ : SuccStruct C) (α : Ordinal.{w})
    [HasIterationOfShape (Shape (Order.succ α)) C] : C :=
  (diagram Φ (Order.succ α)).obj (predIndex α)

/-- The stage immediately after `α` in the ordinal-bounded iteration ending at `α + 1`. -/
noncomputable abbrev succ (Φ : SuccStruct C) (α : Ordinal.{w})
    [HasIterationOfShape (Shape (Order.succ α)) C] : C :=
  (diagram Φ (Order.succ α)).obj (succIndex α)

/-- The canonical identification of the stage after `α` with the successor construction applied
to the `α`-stage. -/
@[stacks 01DM]
noncomputable def succIso (Φ : SuccStruct C) (α : Ordinal.{w})
    [HasIterationOfShape (Shape (Order.succ α)) C] :
    succ Φ α ≅ Φ.succ (pred Φ α) :=
  Φ.iterationFunctorObjSuccIso (predIndex α)
    (not_isMax_predIndex α)

/-- The canonical successor map inside the ordinal-bounded iteration. -/
@[stacks 01DM]
noncomputable def toSucc (Φ : SuccStruct C) (α : Ordinal.{w})
    [HasIterationOfShape (Shape (Order.succ α)) C] :
    pred Φ α ⟶ succ Φ α :=
  Φ.toSucc (pred Φ α) ≫ (succIso Φ α).inv

/-- Identity law for maps inside an ordinal-bounded iteration. -/
@[simp]
theorem map_id (Φ : SuccStruct C) {α β : Ordinal.{w}} (h : α ≤ β)
    [HasIterationOfShape (Shape β) C] :
    map Φ h h le_rfl = 𝟙 (obj Φ h) := sorry

/-- Composition law for maps inside an ordinal-bounded iteration. -/
theorem map_comp (Φ : SuccStruct C) {α₁ α₂ α₃ β : Ordinal.{w}}
    (h₁ : α₁ ≤ β) (h₂ : α₂ ≤ β) (h₃ : α₃ ≤ β)
    (h₁₂ : α₁ ≤ α₂) (h₂₃ : α₂ ≤ α₃)
    [HasIterationOfShape (Shape β) C] :
    map Φ h₁ h₃ (h₁₂.trans h₂₃) = map Φ h₁ h₂ h₁₂ ≫ map Φ h₂ h₃ h₂₃ := sorry

end CategoryTheory.SmallObject.SuccStruct.OrdinalBounded
