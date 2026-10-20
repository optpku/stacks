/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Cofibered.PushforwardComparison
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
import StacksCheckRecall

/-!
# Comparison of fibre categories over a fibre product in C_Λ

A commuting square of pushforwards for a category cofibered in groupoids over `C_Λ` induces the
comparison functor `fiberComparison` into the 2-fibre product of fibre categories.
-/

@[expose] public section

open CategoryTheory Functor Limits CategoricalPullback
open scoped CategoricalPullback

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsFibered.InGroupoids p.op] (χ : p.op.Cleavage)
variable {A A1 A2 P : ArtinianLocalAlgCat Λ k}
variable (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (π1 : P ⟶ A1) (π2 : P ⟶ A2)
variable (h : IsPullback π1 π2 f1 f2)

/- 90.10.1.1: a choice of pushforwards for a category `F` cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` sends a commuting square with vertex a fibre product `A1 ×_A A2`
(available in `C_Λ` when `f2` is surjective, and packaged here by `h`) to the comparison
functor `fiberComparison p χ h.w : p.Fiber P ⥤ (pushforwardFiberFunctor p χ f1) ⊡
(pushforwardFiberFunctor p χ f2)` into the 2-fibre product of fibre categories. -/
@[stacks 06SP]
#check (CategoryTheory.Functor.fiberComparison p χ h.w :
  p.Fiber P ⥤
    (CategoryTheory.Functor.pushforwardFiberFunctor p χ f1) ⊡
      (CategoryTheory.Functor.pushforwardFiberFunctor p χ f2))
