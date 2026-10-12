/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.CrossRefAttribute

/-! @stack 01FI -/

/-!
# Ordered Čech indices

This module owns the purely order-theoretic indexing data for ordered Čech complexes.  It has no
topological, sheaf, or coefficient-category hypotheses.
-/

@[expose] public section

universe v

variable {ι : Type v} [LinearOrder ι]

/-- A degree-`p` ordered Čech index is a strictly increasing `(p + 1)`-tuple. -/
@[stacks 01FI "ordered Cech index"]
abbrev OrderedCechIndex (ι : Type v) [LinearOrder ι] (p : ℕ) : Type v :=
  Fin (p + 1) ↪o ι

/-- A short name for the canonical ordered Čech index in the ambient linear order. -/
abbrev StrictCechTuple (p : ℕ) :=
  OrderedCechIndex ι p

namespace OrderedCechIndex

/-- Strictly increasing tuples in a finite linearly ordered type form a finite type. -/
noncomputable instance instFinite [Finite ι] (p : ℕ) : Finite (OrderedCechIndex ι p) := sorry

/-- Deleting an entry from a strictly increasing tuple remains strictly increasing. -/
@[stacks 01FK "strictness of ordered Cech deletion"]
theorem delete_strictMono {p : ℕ} (σ : OrderedCechIndex ι (p + 1)) (j : Fin (p + 2)) :
    StrictMono (σ ∘ j.succAboveEmb) := sorry

/-- Delete the `j`th entry of a strictly increasing Čech tuple. -/
@[stacks 01FK "ordered Cech tuple deletion"]
def delete {p : ℕ} (σ : OrderedCechIndex ι (p + 1)) (j : Fin (p + 2)) :
    OrderedCechIndex ι p :=
  (Fin.succAboveOrderEmb j).comp σ

/-- The underlying function of a deleted tuple is composition with `Fin.succAboveEmb`. -/
@[simp, stacks 01FK "ordered Cech deletion computation"]
theorem coe_delete {p : ℕ} (σ : OrderedCechIndex ι (p + 1)) (j : Fin (p + 2)) :
    ⇑(σ.delete j) = σ ∘ j.succAboveEmb := sorry

end OrderedCechIndex
