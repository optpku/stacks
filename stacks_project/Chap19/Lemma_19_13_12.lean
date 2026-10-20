/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Derived.InverseSystem
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t w v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A] [IsGrothendieckAbelian.{w} A]

/- Lemma 19.13.12: every compatible inverse system over `ℤ` in `DerivedCategory A`
has a filtered-complex realization. -/
@[stacks 0ESJ] #check
  fun {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system) ↦
    (Realization.nonempty c : Nonempty (Realization c))

end CategoryTheory.FilteredComplex
