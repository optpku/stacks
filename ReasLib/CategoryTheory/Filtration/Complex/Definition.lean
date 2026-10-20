/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered Complexes

A filtered complex is a cochain complex in the category of filtered objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

/-- A filtered complex is a cochain complex in the category of filtered objects. -/
@[stacks 012L]
abbrev FilteredComplex := CochainComplex (FilteredObject 𝒜) ℤ

end CategoryTheory
