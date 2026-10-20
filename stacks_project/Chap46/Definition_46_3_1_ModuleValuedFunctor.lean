/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor

@[expose] public section

open CategoryTheory

universe u v

variable (A : CommRingCat.{u})

#check (ModuleValuedFunctor.{u, v} A : Type (max (u + 1) (v + 1)))

variable (F G : ModuleValuedFunctor.{u, v} A)

#check (ModuleValuedFunctor.Hom F G : Type (max (u + 1) v))
