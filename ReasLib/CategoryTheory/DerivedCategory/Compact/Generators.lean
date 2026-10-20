module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.FiniteCoproductClosure
public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Retract
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compact objects from compact generators

This file gives the bounded-complex presentation of compact objects in the derived category of a
Grothendieck abelian category. The generating family is represented by an object property, its
finite direct sums by `ObjectProperty.additiveClosure`, and direct summands by `Retract`.
-/

@[expose] public section

open CategoryTheory.ObjectProperty

noncomputable section

universe g w v u

namespace CategoryTheory.IsCompactObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{w} A]
variable [IsGrothendieckAbelian.{g} A]

/-- Lemma 21.52.1 (094B): a compact object in the derived category of a Grothendieck abelian
category is a retract of the derived image of a bounded complex whose terms are finite direct
sums of members of any separating compact family. -/
@[stacks 094B]
theorem exists_retract_bounded_additiveClosure
    (P : ObjectProperty A) {K : DerivedCategory A}
    (hK : _root_.CategoryTheory.IsCompactObject K)
    (hgen : P.IsSeparating)
    (hcompact : ∀ X : A, P X → _root_.CategoryTheory.IsCompactObject X) :
    ∃ L : CochainComplex.Bounded A,
      (∀ i : ℤ, P.additiveClosure (L.obj.X i)) ∧
        Nonempty (Retract K (DerivedCategory.Q.obj L.obj)) := sorry

end CategoryTheory.IsCompactObject
