/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.NatTrans

/-!
# Lemma 90.11.13

A morphism of functors satisfying the hypotheses of Lemma 90.11.8 induces
`R`-linear maps on the values `F(R[M])`, and in particular on `F(R[ε])`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open TrivSqZeroExt

universe u

namespace CategoryTheory.Functor

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable {P : ObjectProperty (Over (CommAlgCat.of S R))}
variable [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]

/-- The additive group structure of Lemma 90.11.8 on `F(R[M])`. -/
instance instAddCommGroup_obj_fgLift {F : P.FullSubcategory ⥤ Type u}
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds]
    (M : FGModuleCat.{u} R) :
    AddCommGroup (F.obj ((fgLift P).obj M)) :=
  instAddCommGroup (fgEval P F) M

/-- The `R`-module structure of Lemma 90.11.8 on `F(R[M])`. -/
instance instModule_obj_fgLift {F : P.FullSubcategory ⥤ Type u}
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds]
    (M : FGModuleCat.{u} R) :
    Module R (F.obj ((fgLift P).obj M)) :=
  instModule (fgEval P F) M

/- Lemma 90.11.13 (1): If `F, G : C ⥤ Type` satisfy the hypotheses of
Lemma 90.11.8 and `t : F ⟶ G`, then for every finitely generated `R`-module
`M` the component `t.app ((fgLift P).obj M) : F(R[M]) → G(R[M])` is an
`R`-module map, where `F(R[M]) = (fgEval P F).obj M` and
`G(R[M]) = (fgEval P G).obj M` carry the `R`-module structures of
Lemma 90.11.8. -/
@[stacks 06ID]
#check (CategoryTheory.Functor.isLinearMap_app_fgLift :
  ∀ {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    {P : ObjectProperty (Over (CommAlgCat.of S R))}
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    {F G : P.FullSubcategory ⥤ Type u}
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds]
    [Unique (G.obj (overSelfObj P))] [G.BijectiveOnFGSquareZeroProds]
    (t : F ⟶ G) (M : FGModuleCat.{u} R),
    IsLinearMap R
      (t.app ((fgLift P).obj M) : (fgEval P F).obj M → (fgEval P G).obj M))

/- Lemma 90.11.13 (2): In particular, writing `R[ε] = R[R] = DualNumber R` as
`(fgLift P).obj (FGModuleCat.of R R)`, the component
`t.app ((fgLift P).obj (FGModuleCat.of R R)) : F(R[ε]) → G(R[ε])` is an
`R`-module map for the structures of Lemma 90.11.8. -/
@[stacks 06ID]
#check (CategoryTheory.Functor.isLinearMap_app_fgLift_self :
  ∀ {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    {P : ObjectProperty (Over (CommAlgCat.of S R))}
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    {F G : P.FullSubcategory ⥤ Type u}
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds]
    [Unique (G.obj (overSelfObj P))] [G.BijectiveOnFGSquareZeroProds]
    (t : F ⟶ G),
    IsLinearMap R
      (t.app ((fgLift P).obj (FGModuleCat.of R R)) :
        (fgEval P F).obj (FGModuleCat.of R R) →
          (fgEval P G).obj (FGModuleCat.of R R)))

end CategoryTheory.Functor
