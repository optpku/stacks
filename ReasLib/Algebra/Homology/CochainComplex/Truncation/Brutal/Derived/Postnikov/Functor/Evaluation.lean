/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov.Functor.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Functor.Evaluation

/-!
# Evaluation of Functorial Finite Brutal Postnikov Systems

This leaf identifies row, auxiliary-object, and triangle evaluation after finite brutal
restriction with evaluation of the underlying sequential Postnikov tower.
-/

@[expose] public section

open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Finite

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Evaluating a finite brutal row is evaluation of the underlying Postnikov tower at the
corresponding reversed index. -/
@[stacks 0D8Z "row evaluation of functorial finite brutal Postnikov systems"]
theorem functor_comp_row (n : ℕ) (i : Fin (n + 1)) :
    functor A n ⋙ PostnikovSystem.Total.row (DerivedCategory A) n i =
      _root_.CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.functor A ⋙
        PostnikovSystem.Tower.Stage.row (DerivedCategory A)
          (PostnikovSystem.Tower.Finite.index i) := sorry

/-- Evaluating a finite brutal auxiliary object is evaluation of the underlying Postnikov tower
at the corresponding reversed index. -/
@[stacks 0D8Z "auxiliary evaluation of functorial finite brutal Postnikov systems"]
theorem functor_comp_aux (n : ℕ) (i : Fin (n + 1)) :
    functor A n ⋙ PostnikovSystem.Total.aux (DerivedCategory A) n i =
      _root_.CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.functor A ⋙
        PostnikovSystem.Tower.Stage.aux (DerivedCategory A)
          (PostnikovSystem.Tower.Finite.index i) := sorry

/-- Evaluating a finite brutal stage triangle is evaluation of the underlying Postnikov tower
at the corresponding reversed index. -/
@[stacks 0D8Z "triangle evaluation of functorial finite brutal Postnikov systems"]
theorem functor_comp_triangle (n : ℕ) (i : Fin n) :
    functor A n ⋙ PostnikovSystem.Total.triangle (DerivedCategory A) n i =
      _root_.CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.functor A ⋙
        PostnikovSystem.Tower.Stage.triangle (DerivedCategory A)
          (PostnikovSystem.Tower.Finite.index i) := sorry

end CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Finite
