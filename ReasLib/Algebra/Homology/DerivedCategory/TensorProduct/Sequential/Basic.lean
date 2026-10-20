/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products of sequential module systems

@stack 091L

This leaf owns only the existence of the pointwise derived tensor product on
sequential inverse systems of modules.  Pro-isomorphism and derived-limit
compatibility live in the corresponding higher-level leaves.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/-- Pointwise tensoring on sequential inverse systems of `R`-modules admits the fixed-left and
fixed-right unbounded derived tensor constructions. -/
@[stacks 091L "derived tensor on sequential module systems"]
instance SequentialModule.hasDerivedTensor :
    DerivedTensor.Has (C := SequentialInverseSystem (ModuleCat R)) := sorry

end CategoryTheory.DerivedCategory
