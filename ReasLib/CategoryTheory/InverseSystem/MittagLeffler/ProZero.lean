module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.AddCommGrp
public import ReasLib.CategoryTheory.Pro.Sequential.Zero
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero sequential pro-objects of abelian groups

This leaf is the bridge between the presentation-independent `Pro.HasValue` interface and the
inverse-limit/derived-limit criteria used for sequential systems of abelian groups.
@stack 091C
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe v

namespace CategoryTheory.Pro.HasValue

/-- For a sequential inverse system of abelian groups, the zero pro-value is equivalent to the
inverse limit being zero and the system satisfying the Mittag-Leffler condition. -/
theorem zero_iff_limit_isZero_and_isMittagLeffler
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    Pro.HasValue A (0 : AddCommGrpCat) ↔
      IsZero (limit A) ∧ A.IsMittagLeffler := sorry

/-- Lemma 15.87.16 [091C]: a sequential inverse system of abelian groups has zero pro-value
exactly when its inverse limit, its canonical Milnor cokernel, and the canonical Milnor cokernel
of its stagewise countable coproduct all vanish. -/
@[stacks 091C]
theorem zero_iff_limit_and_r1Vanishing_of_countableCoproduct
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    Pro.HasValue A (0 : AddCommGrpCat) ↔
      IsZero (limit A) ∧
        IsZero (SequentialInverseSystem.Milnor.ProductCone.canonicalR1 A) ∧
          IsZero (SequentialInverseSystem.Milnor.ProductCone.canonicalR1
            A.countableCoproduct) := sorry

end CategoryTheory.Pro.HasValue
