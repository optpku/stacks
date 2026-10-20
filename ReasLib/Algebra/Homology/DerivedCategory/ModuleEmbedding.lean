/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat

@[expose] public section

/-!
# Module embeddings into derived categories

This leaf owns the standard degree-zero embedding of modules into their unbounded derived
category.  It is kept separate from properties such as perfectness or Tor-amplitude so that
derived-category APIs can share the same canonical bridge without importing unrelated finiteness
infrastructure.
@stack 064M
-/

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

section

variable {R : Type u} [Ring R]

/-- The canonical degree-zero embedding `ModuleCat R ⥤ DerivedCategory (ModuleCat R)`. -/
@[stacks 064M "degree-zero module embedding"]
abbrev single0Functor : ModuleCat R ⥤ DerivedCategory (ModuleCat R) :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The degree-zero derived object associated to an `R`-module. -/
@[stacks 064M "degree-zero derived module"]
abbrev single0 (M : ModuleCat R) : DerivedCategory (ModuleCat R) :=
  single0Functor.obj M

end

end CategoryTheory.ModuleCat
