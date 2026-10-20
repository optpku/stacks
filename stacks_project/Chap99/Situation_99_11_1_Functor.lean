/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import stacks_project.Chap78.Remark_78_19_2_Quotient
public import stacks_project.Chap99.Situation_99_5_1_Fiber
public import stacks_project.Chap99.Situation_99_11_1_Pullback

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative

/-! # The relative Picard functor of a morphism of algebraic spaces -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

/-- The relative Picard functor is the fppf sheafification of the presheaf of
Picard groups of scheme-valued fibers. -/
abbrev functor {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) :
    Sheaf (SchemesOver.fppfTopology B) (Type (u + 1)) :=
  AlgebraicGeometry.AlgebraicSpace.picardFunctor f

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
