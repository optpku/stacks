/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.DiagonalModels.Concrete

/-!
# Comparisons with the iterated diagonal model

The specified forward comparison from an arbitrary square over the diagonal cospan to the
iterated concrete model, together with its projection computations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe vC vS vC' uC uS uC'

namespace CategoryTheory.Limits

noncomputable section

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {G₁ G₂ : C ⥤ S}

variable {C' : Type uC'} [Category.{vC'} C']
variable (P : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) C')

/- The source square is over `G₁.prod' G₂` and `Functor.diag S`; its specified comparison
first enters the direct diagonal model and then applies the concrete model comparison. -/

namespace CategoricalPullback.CatCommSqOver

/-- The specified comparison from an arbitrary source square to the iterated pullback model. -/
def iteratedDiagonalComparison :
    C' ⥤ CategoricalPullback.DiagonalModel.iterated G₁ G₂ :=
  P.comparison ⋙ CategoricalPullback.DiagonalModel.comparison G₁ G₂

namespace iteratedDiagonalComparison

/-- The first inner object of the iterated comparison is the `C`-leg of the source square. -/
@[simp] theorem obj.fstFst (x : C') :
    (P.iteratedDiagonalComparison.obj x).fst.fst = P.fst.obj x := sorry

/-- The second inner object of the iterated comparison is also the `C`-leg of the source
square. -/
@[simp] theorem obj.fstSnd (x : C') :
    (P.iteratedDiagonalComparison.obj x).fst.snd = P.fst.obj x := sorry

/-- The inner structural isomorphism of the iterated comparison is induced by the two
components of the source square's structural isomorphism. -/
@[simp] theorem obj.fstIso (x : C') :
    (P.iteratedDiagonalComparison.obj x).fst.iso =
      (CategoryTheory.Prod.fst S S).mapIso (P.iso.app x) ≪≫
        ((CategoryTheory.Prod.snd S S).mapIso (P.iso.app x)).symm := sorry

/-- The outer object of the iterated comparison is the `C`-leg of the source square. -/
@[simp] theorem obj.snd (x : C') :
    (P.iteratedDiagonalComparison.obj x).snd = P.fst.obj x := sorry

/-- The outer structural isomorphism of the iterated comparison is the identity on the source
square's `C`-leg. -/
@[simp] theorem obj.iso (x : C') :
    (P.iteratedDiagonalComparison.obj x).iso =
      Iso.refl ((Functor.diag C).obj (P.fst.obj x)) := sorry

/-- The first inner map of the iterated comparison is the map of the source square's `C`-leg. -/
@[simp] theorem map.fstFst {x y : C'} (f : x ⟶ y) :
    (P.iteratedDiagonalComparison.map f).fst.fst = P.fst.map f := sorry

/-- The second inner map of the iterated comparison is the map of the source square's `C`-leg. -/
@[simp] theorem map.fstSnd {x y : C'} (f : x ⟶ y) :
    (P.iteratedDiagonalComparison.map f).fst.snd = P.fst.map f := sorry

/-- The outer map of the iterated comparison is the map of the source square's `C`-leg. -/
@[simp] theorem map.snd {x y : C'} (f : x ⟶ y) :
    (P.iteratedDiagonalComparison.map f).snd = P.fst.map f := sorry

end iteratedDiagonalComparison

end CategoricalPullback.CatCommSqOver

end

end CategoryTheory.Limits
