/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The product-power functor sends a module to a product of copies indexed by `I`. -/
noncomputable def piConst (I : Type u) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  Functor.const (Discrete I) ⋙ lim

/-- The product-power functor is additive. -/
noncomputable instance piConst_additive (I : Type u) : (piConst R I).Additive := sorry

/-- The product-power functor is `R`-linear. -/
noncomputable instance piConst_linear (I : Type u) : (piConst R I).Linear R := sorry

/-- The product-power functor preserves finite colimits. -/
noncomputable instance piConst_preservesFiniteColimits (I : Type u) :
    PreservesFiniteColimits (piConst R I) :=
  comp_preservesFiniteColimits (Functor.const (Discrete I)) lim

end ModuleCat
