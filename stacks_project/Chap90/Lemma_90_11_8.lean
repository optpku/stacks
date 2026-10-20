/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.Evaluation

open CategoryTheory

universe u

/- Lemma 90.11.8: Let `R` be an `S`-algebra, and let `C` be a strictly full
subcategory of `S`-Alg/`R` containing `R[M]` for all finitely generated
`R`-modules `M`. Let `F : C ⥤ Type` be a functor. Suppose that `F(R)` is a
one-element set and that for any finitely generated `R`-modules `M, N` the
induced map `F(R[M] ×_R R[N]) ⟶ F(R[M]) × F(R[N])` is a bijection. Then
`F(R[M])` has a natural `R`-module structure for any finitely generated
`R`-module `M`, expressed by the unique module-linear lift of `M ↦ F(R[M])`. -/
@[stacks 06IA]
#check (CategoryTheory.Functor.module_fgEval :
  ∀ {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) [Unique (F.obj (TrivSqZeroExt.overSelfObj P))]
    [F.BijectiveOnFGSquareZeroProds],
    ∃! G : FGModuleCat.{u} R ⥤ ModuleCat.{u} R,
      G.ModuleLinear R ∧ G ⋙ forget (ModuleCat.{u} R) = CategoryTheory.Functor.fgEval P F)
