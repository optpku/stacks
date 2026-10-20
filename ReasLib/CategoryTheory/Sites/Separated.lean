/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Presieve

/-- A type-valued presheaf is separated for a topology exactly when restriction
maps from every covering presieve are injective. -/
theorem isSeparated_iff_injective_restriction
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ Type w) :
    IsSeparated J F ↔
      ∀ (U : C) (R : Presieve U), Sieve.generate R ∈ J U →
        Function.Injective
          (fun sectionValue : F.obj (Opposite.op U) =>
            fun (V : C) (arrow : V ⟶ U) (_ : R arrow) =>
              F.map arrow.op sectionValue) := sorry

end CategoryTheory.Presieve
