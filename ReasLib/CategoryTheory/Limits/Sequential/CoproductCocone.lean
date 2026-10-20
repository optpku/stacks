/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.ColimitCocone.Discrete.Iso
public import ReasLib.CategoryTheory.Limits.Sequential

@[expose] public section

/-!
# Telescope Maps on Explicit Coproduct Cocones

This leaf formulates the telescope endomorphism of a sequential diagram on a
supplied coproduct `ColimitCocone`. General maps between explicit colimit cocones
are provided by `Limits.ColimitCocone`; this leaf retains the discrete-coproduct
computations and telescope-specific naturality API.
-/

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Limits.Sequential.CoproductCocone

variable {C : Type u} [Category.{v} C]

/-- The `n`th inclusion into an explicitly supplied coproduct cocone. -/
def inclusion {K : ℕ ⥤ C} (P : ColimitCocone (Discrete.functor K.obj)) (n : ℕ) :
    K.obj n ⟶ P.cocone.pt :=
  P.cocone.ι.app ⟨n⟩

/-- On the colimit cocone selected by a `HasCoproduct` instance, the explicit inclusion is the
usual coproduct inclusion. -/
@[simp]
theorem inclusion_getColimitCocone (K : ℕ ⥤ C) [HasCoproduct K.obj] (n : ℕ) :
    inclusion (getColimitCocone (Discrete.functor K.obj)) n = Sigma.ι K.obj n := sorry

/-- The morphism out of an explicit coproduct cocone determined by its family of legs. -/
def desc {K : ℕ ⥤ C} (P : ColimitCocone (Discrete.functor K.obj)) {X : C}
    (f : ∀ n : ℕ, K.obj n ⟶ X) : P.cocone.pt ⟶ X :=
  P.isColimit.desc (Cofan.mk X f)

/-- The descent from an explicit coproduct cocone has the prescribed leg at every index. -/
@[reassoc (attr := simp)]
theorem inclusion_comp_desc {K : ℕ ⥤ C}
    (P : ColimitCocone (Discrete.functor K.obj)) {X : C}
    (f : ∀ n : ℕ, K.obj n ⟶ X) (n : ℕ) :
    inclusion P n ≫ desc P f = f n := sorry

/-- On the colimit cocone selected by a `HasCoproduct` instance, explicit descent is the usual
coproduct descent. -/
@[simp]
theorem desc_getColimitCocone (K : ℕ ⥤ C) [HasCoproduct K.obj] {X : C}
    (f : ∀ n : ℕ, K.obj n ⟶ X) :
    desc (getColimitCocone (Discrete.functor K.obj)) f = Sigma.desc f := sorry

/-- A morphism out of an explicit coproduct cocone is determined by its composites with all
inclusions. -/
theorem desc_uniq {K : ℕ ⥤ C} (P : ColimitCocone (Discrete.functor K.obj))
    {X : C} (f : ∀ n : ℕ, K.obj n ⟶ X) (g : P.cocone.pt ⟶ X)
    (hg : ∀ n : ℕ, inclusion P n ≫ g = f n) :
    g = desc P f := sorry

section

variable [Preadditive C]

/-- Stacks 090Z: the telescope endomorphism on an explicitly supplied coproduct cocone. -/
@[stacks 090Z]
def telescopeMap (K : ℕ ⥤ C) (P : ColimitCocone (Discrete.functor K.obj)) :
    P.cocone.pt ⟶ P.cocone.pt :=
  desc P fun n ↦
    inclusion P n - K.map (homOfLE (Nat.le_succ n)) ≫ inclusion P (n + 1)

/-- The `n`th inclusion followed by the explicit-cocone telescope map is the difference of the
current inclusion and the transition followed by the successor inclusion. -/
@[reassoc (attr := simp)]
theorem inclusion_comp_telescopeMap (K : ℕ ⥤ C)
    (P : ColimitCocone (Discrete.functor K.obj)) (n : ℕ) :
    inclusion P n ≫ telescopeMap K P =
      inclusion P n - K.map (homOfLE (Nat.le_succ n)) ≫ inclusion P (n + 1) := sorry

/-- On the coproduct cocone selected by a `HasCoproduct` instance, the explicit-cocone
telescope map is the canonical telescope map. -/
@[simp]
theorem telescopeMap_getColimitCocone (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    telescopeMap K (getColimitCocone (Discrete.functor K.obj)) =
      CategoryTheory.Limits.Sequential.telescopeMap K := sorry

/-- The explicit telescope map vanishes after a descent whose legs form a cocone over the
sequential diagram. -/
@[reassoc]
theorem telescopeMap_comp_desc (K : ℕ ⥤ C)
    (P : ColimitCocone (Discrete.functor K.obj)) {X : C}
    (f : ∀ n : ℕ, K.obj n ⟶ X)
    (hf : ∀ n : ℕ, K.map (homOfLE (Nat.le_succ n)) ≫ f (n + 1) = f n) :
    telescopeMap K P ≫ desc P f = 0 := sorry

end

section

variable [Preadditive C]

/-- The telescope endomorphism is natural for maps between explicitly supplied coproduct
cocones. -/
@[reassoc]
theorem telescopeMap_naturality {K L : ℕ ⥤ C}
    (P : ColimitCocone (Discrete.functor K.obj))
    (Q : ColimitCocone (Discrete.functor L.obj)) (f : K ⟶ L) :
    telescopeMap K P ≫ ColimitCocone.Discrete.map P Q f.app =
      ColimitCocone.Discrete.map P Q f.app ≫ telescopeMap L Q := sorry

end

end CategoryTheory.Limits.Sequential.CoproductCocone
