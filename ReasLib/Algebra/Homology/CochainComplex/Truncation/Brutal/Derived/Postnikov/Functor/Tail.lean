/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov.Functor.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Functor.Tail

/-!
# Successor Coherence for Functorial Brutal Postnikov Systems

This leaf records compatibility of finite brutal Postnikov-system restriction
with the total tail functor.
-/

@[expose] public section

open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Finite

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Successor finite brutal restriction followed by total truncation is the preceding finite
brutal Postnikov-system functor. -/
@[stacks 0D8Z "successor coherence of finite brutal Postnikov systems"]
theorem functor_succ (n : ℕ) :
    functor A (n + 1) ⋙ PostnikovSystem.Total.tail (DerivedCategory A) n =
      functor A n := sorry

end CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Finite
