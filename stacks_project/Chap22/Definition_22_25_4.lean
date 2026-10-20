/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Graded.Biproduct
import StacksCheckRecall

universe x w v u

open CategoryTheory

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable [GradedCategory R C ι]
variable {x y z : C} (i : x ⟶ z) (j : y ⟶ z) (p : z ⟶ x) (q : z ⟶ y)

/- Definition 22.25.4 [09P2]: a split binary direct sum whose structure morphisms have
degree zero is canonically represented by `GradedCategory.IsGradedDirectSum`. -/
@[stacks 09P2] #check
  (GradedCategory.IsGradedDirectSum (R := R) (ι := ι) i j p q : Prop)
