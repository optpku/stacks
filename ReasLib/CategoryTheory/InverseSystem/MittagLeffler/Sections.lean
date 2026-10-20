module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections of Countable Mittag-Leffler Inverse Systems

@stack 0597

This leaf records the set-valued countable Mittag-Leffler theorem.  It belongs to the
Mathlib `Functor.IsMittagLeffler` API rather than to a particular algebraic inverse-system
application.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Functor.IsMittagLeffler

/-- Lemma 10.86.3: a Mittag-Leffler inverse system of nonempty sets indexed by a countable
directed preorder has a nonempty set of compatible sections.  This explicit form is convenient
when stagewise nonemptiness is available as ordinary theorem data rather than as an instance. -/
@[stacks 0597]
theorem nonempty_sections_of_countable_of_forall_nonempty
    {I : Type u} [Preorder I] [IsDirectedOrder I] [Countable I]
    {A : OrderDual I ⥤ Type v} (hA : A.IsMittagLeffler)
    (h_nonempty : ∀ i : OrderDual I, Nonempty (A.obj i)) :
    A.sections.Nonempty := sorry

/-- The instance-facing form of `nonempty_sections_of_countable_of_forall_nonempty`. -/
@[stacks 0597 "instance-facing section existence"]
theorem nonempty_sections_of_countable
    {I : Type u} [Preorder I] [IsDirectedOrder I] [Countable I]
    {A : OrderDual I ⥤ Type v} (hA : A.IsMittagLeffler)
    [∀ i : OrderDual I, Nonempty (A.obj i)] :
    A.sections.Nonempty := sorry

end CategoryTheory.Functor.IsMittagLeffler
