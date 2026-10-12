/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Five-Term Sequences of Contravariant Cohomological Functors

@stack 0148

A contravariant functor is represented by the homological functor on the
opposite category supplied by `Functor.rightOp`.  This leaf exposes the
centered five-term row as concrete data and records its exactness separately.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Cohomological

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : Dᵒᵖ ⥤ A) [H.rightOp.IsHomological]
  [H.rightOp.ShiftSequence ℤ]

/-- The centered five-term row attached to a triangle by a contravariant
cohomological functor. -/
@[stacks 0148 "contravariant cohomological five-term row"]
noncomputable def fiveTerm (T : Triangle D) (n : ℤ) :
    ComposableArrows A 4 :=
  mk₄ (((H.rightOp.shift (n + 1)).map T.mor₁).unop)
    ((H.rightOp.homologySequenceδ T n (n + 1) rfl).unop)
    (((H.rightOp.shift n).map T.mor₂).unop)
    (((H.rightOp.shift n).map T.mor₁).unop)

/-- 13.3.5.1 (Stacks `0148`): the centered five-term row of a
contravariant cohomological functor is exact on distinguished triangles. -/
@[stacks 0148]
theorem fiveTerm_exact (T : Triangle D) (hT : T ∈ distTriang D) (n : ℤ) :
    (fiveTerm H T n).Exact := sorry

end CategoryTheory.Functor.Cohomological
