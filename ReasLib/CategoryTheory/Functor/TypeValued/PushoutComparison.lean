/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]

/-- The restriction map from a Type-valued presheaf on the vertex of a
commutative square to the pullback of its restrictions along the two legs. -/
def pushoutComparison (G : Cᵒᵖ ⥤ Type w)
    {Z Z' Y Y' : C} {i : Z ⟶ Z'} {g : Z ⟶ Y}
    {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'} (h : i ≫ inl = g ≫ inr) :
    G.obj (op Y') ⟶ pullback (G.map g.op) (G.map i.op) :=
  pullback.lift (G.map inr.op) (G.map inl.op)
    (((G.map_comp inr.op g.op).symm.trans
        (congrArg G.map (congrArg (fun k ↦ k.op) h.symm))).trans
      (G.map_comp inl.op i.op))

/-- The first projection of the restriction comparison is restriction along `inr`. -/
theorem pushoutComparison_fst (G : Cᵒᵖ ⥤ Type w)
    {Z Z' Y Y' : C} {i : Z ⟶ Z'} {g : Z ⟶ Y}
    {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'} (h : i ≫ inl = g ≫ inr) :
    pushoutComparison G h ≫ pullback.fst _ _ = G.map inr.op := sorry

/-- The second projection of the restriction comparison is restriction along `inl`. -/
theorem pushoutComparison_snd (G : Cᵒᵖ ⥤ Type w)
    {Z Z' Y Y' : C} {i : Z ⟶ Z'} {g : Z ⟶ Y}
    {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'} (h : i ≫ inl = g ≫ inr) :
    pushoutComparison G h ≫ pullback.snd _ _ = G.map inl.op := sorry

end CategoryTheory.FunctorToTypes
