/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Coproducts of sequential inverse systems

This leaf owns the stagewise countable-coproduct endofunctor on sequential inverse systems,
along with its objectwise and coproduct-injection computations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

/-- The endofunctor on sequential inverse systems obtained by taking the countable coproduct at
every stage. -/
noncomputable def countableCoproductFunctor [HasCountableCoproducts A] :
    SequentialInverseSystem A ⥤ SequentialInverseSystem A :=
  (Functor.whiskeringRight ℕᵒᵖ A A).obj ((Functor.const (Discrete ℕ)) ⋙ colim)

/-- The sequential inverse system obtained from `F` by taking a countable coproduct at every
stage. -/
noncomputable def countableCoproduct [HasCountableCoproducts A] (F : SequentialInverseSystem A) :
    SequentialInverseSystem A :=
  (countableCoproductFunctor (A := A)).obj F

/-- A morphism of sequential inverse systems induces a morphism between their stagewise countable
coproduct systems. -/
noncomputable def countableCoproductMap [HasCountableCoproducts A]
    {F G : SequentialInverseSystem A} (α : F ⟶ G) :
    F.countableCoproduct ⟶ G.countableCoproduct :=
  (countableCoproductFunctor (A := A)).map α

/-- Evaluating the stagewise countable-coproduct inverse system at `n` gives the canonical
countable coproduct of copies of `F.obj n`. -/
@[simp]
theorem countableCoproduct_obj [HasCountableCoproducts A]
    (F : SequentialInverseSystem A) (n : ℕᵒᵖ) :
    F.countableCoproduct.obj n = ∐ fun _ : ℕ ↦ F.obj n :=
  sorry

/-- The component of `countableCoproductMap α` at `n` is the colimit map induced by the constant
diagram of `α.app n`. -/
@[simp]
theorem countableCoproductMap_app [HasCountableCoproducts A]
    {F G : SequentialInverseSystem A} (α : F ⟶ G) (n : ℕᵒᵖ) :
    (countableCoproductMap α).app n =
      colim.map ((Functor.const (Discrete ℕ)).map (α.app n)) :=
  sorry

/-- The map on stagewise countable coproducts carries the `m`th coproduct injection to the
corresponding injection after `α.app n`. -/
@[reassoc]
theorem countableCoproductMap_ι [HasCountableCoproducts A]
    {F G : SequentialInverseSystem A} (α : F ⟶ G) (m : ℕ) (n : ℕᵒᵖ) :
    Sigma.ι (fun _ : ℕ ↦ F.obj n) m ≫ (countableCoproductMap α).app n =
      α.app n ≫ Sigma.ι (fun _ : ℕ ↦ G.obj n) m :=
  sorry

end SequentialInverseSystem

end CategoryTheory
