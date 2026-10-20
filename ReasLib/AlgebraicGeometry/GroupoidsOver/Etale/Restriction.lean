/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.CategoryTheory.Fibered.Cleavage.SliceSection
public import ReasLib.CategoryTheory.Presheaf.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Small-étale evaluation of a groupoid fibration

An object `x` of a category fibred in groupoids over `(Sch/S)_fppf` determines
cartesian lifts of étale neighborhoods of `U = p(x)`. Precomposition with this
evaluation functor restricts a presheaf on the total category to the small étale
site of `U`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

noncomputable section

universe u a b

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The object of `Over (p(x))` associated to an étale neighborhood of
`U = (X.p.obj x).left`. -/
def etaleOver (x : X.total) (V' : (X.p.obj x).left.Etale) :
    Over (X.p.obj x) :=
  (Over.iteratedSliceBackward (X.p.obj x)).obj
    ((Scheme.Etale.forget (X.p.obj x).left).obj V')

/-- Evaluation of an object `x` of `X` on the small étale site of `U = p(x)`,
sending an étale neighborhood `V' → U` to the selected cartesian lift of `x`.
This is the total functor of the 2-Yoneda representative of `x`, precomposed
with `Scheme.Etale.forget` and `Over.iteratedSliceBackward`. -/
def smallEtaleEval (x : X.total) : (X.p.obj x).left.Etale ⥤ X.total :=
  Scheme.Etale.forget (X.p.obj x).left ⋙
    Over.iteratedSliceBackward (X.p.obj x) ⋙
      Cleavage.SliceSection.total (Cleavage.ofIsFibered X.p) (X.p.obj x) ⟨x, rfl⟩

/-- `smallEtaleEval` sends an étale neighborhood to the selected cartesian lift
of `x` along `etaleOver x V'`. -/
theorem smallEtaleEval_obj (x : X.total) (V' : (X.p.obj x).left.Etale) :
    (smallEtaleEval x).obj V' =
      (Cleavage.SliceSection.total (Cleavage.ofIsFibered X.p) (X.p.obj x)
          ⟨x, rfl⟩).obj (etaleOver x V') :=
  sorry

/-- Restriction of an `A`-valued presheaf on the total category of `X` to the
small étale site of `U = p(x)`. -/
def restrictSmallEtale {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) : (X.p.obj x).left.Etaleᵒᵖ ⥤ A :=
  (smallEtaleEval x).op ⋙ F

/-- Sections of the small-étale restriction over `V'` are the sections of `F` on
the cartesian lift of `x`. -/
theorem restrictSmallEtale_obj {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) (V' : (X.p.obj x).left.Etale) :
    (restrictSmallEtale x F).obj (Opposite.op V') =
      F.obj (Opposite.op ((smallEtaleEval x).obj V')) :=
  sorry

/-- Restriction maps of `restrictSmallEtale` are the images under `F` of the
evaluation maps of `smallEtaleEval`. -/
theorem restrictSmallEtale_map {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) {V' W' : (X.p.obj x).left.Etale} (f : V' ⟶ W') :
    (restrictSmallEtale x F).map (Opposite.op f) =
      F.map (Opposite.op ((smallEtaleEval x).map f)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
