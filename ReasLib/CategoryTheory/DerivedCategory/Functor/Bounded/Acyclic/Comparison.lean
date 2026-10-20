module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt

@[expose] public section

/-!
# Bounded and Unbounded Acyclicity Comparison

The bounded-below and unbounded right-acyclicity predicates agree on objects and termwise on
bounded-below complexes.  The bounded-above left-derived statements are exposed symmetrically.
These comparisons depend only on the generic pointwise computation comparison, not on a chosen
resolution class.
-/

open CategoryTheory
open ComplexShape

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

/-- On degree-zero objects, unbounded and bounded-below right acyclicity are equivalent. -/
@[stacks 015C "bounded/unbounded right-acyclicity comparison"]
theorem RightAcyclic.iff_boundedBelow (X : A) :
    RightAcyclic F X ↔ RightAcyclic.Bounded F X := sorry

/-- A bounded-below complex is termwise right acyclic in the unbounded sense exactly when it is
termwise right acyclic for the bounded-below derived functor. -/
theorem RightAcyclic.Termwise.iff_boundedBelow
    (K : HomotopyCategory.Plus A) :
    RightAcyclic.Termwise F K ↔ RightAcyclic.Bounded.Termwise F K := sorry

/-- On degree-zero objects, unbounded and bounded-above left acyclicity are equivalent. -/
theorem LeftAcyclic.iff_boundedAbove (X : A) :
    LeftAcyclic F X ↔ LeftAcyclic.Bounded F X := sorry

/-- A bounded-above complex is termwise left acyclic in the unbounded sense exactly when it is
termwise left acyclic for the bounded-above derived functor. -/
theorem LeftAcyclic.Termwise.iff_boundedAbove
    (K : HomotopyCategory.Minus A) :
    LeftAcyclic.Termwise F K ↔ LeftAcyclic.Bounded.Termwise F K := sorry

end CategoryTheory.Functor
