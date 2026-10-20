/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Derived.Bifiltered
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t w v u

namespace CategoryTheory.BifilteredComplex.Realization

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{t} A] [IsGrothendieckAbelian.{w} A]

/- Lemma 19.13.13: two inverse systems with compatible maps to the same derived object
have a common bifiltered-complex realization. -/
@[stacks 0ESK] #check
  fun {system system' : ℤᵒᵖ ⥤ DerivedCategory A} (E : DerivedCategory A)
      (π : system ⟶ (Functor.const ℤᵒᵖ).obj E)
      (π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E) ↦
    (nonempty E π π' : Nonempty (BifilteredComplex.Realization E π π'))

end CategoryTheory.BifilteredComplex.Realization
