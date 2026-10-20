/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.Algebra.Module.Graded.Left.Category
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely generated left graded modules

This leaf defines finite generation as an object property of the category of left graded modules.
-/

@[expose] public section

universe x w v u

namespace GradedModule.Left

variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]

/-- The object property of left graded modules whose underlying `A`-module is finitely generated. -/
@[stacks 052N "finitely generated left graded module object property"]
def isFG (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (κ : Type x := ι) [DecidableEq κ] [AddAction ι κ] :
    CategoryTheory.ObjectProperty (Left.{x, w, v, u} 𝒜 κ) :=
  fun M ↦ Module.Finite A M

/-- The full subcategory of finitely generated left graded modules. -/
@[stacks 052N "category of finitely generated left graded modules"]
abbrev FG (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (κ : Type x := ι) [DecidableEq κ] [AddAction ι κ] :=
  (isFG.{x, w, v, u} (κ := κ) 𝒜).FullSubcategory

end GradedModule.Left
