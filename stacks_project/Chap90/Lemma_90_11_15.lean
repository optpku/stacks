/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.Tensor
import StacksCheckRecall

/-!
# Lemma 90.11.15

Under the hypotheses of Lemma 90.11.8, with `R = K` a field, the canonical
comparison `TF ⊗[K] V → F(K[V])` is bijective for every finite-dimensional
`K`-vector space `V`.
-/

open CategoryTheory
open TrivSqZeroExt

universe u

/- Lemma 90.11.15: The canonical comparison identifies `F(K[V])` with
`TF ⊗[K] V` for every finite-dimensional `K`-vector space `V`. -/
@[stacks 06IE]
#check (CategoryTheory.Functor.bijective_tangentSpaceTensor :
  ∀ {S K : Type u} [CommRing S] [Field K] [Algebra S K]
    {P : ObjectProperty (Over (CommAlgCat.of S K))}
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds]
    (V : FGModuleCat.{u} K),
    Function.Bijective (CategoryTheory.Functor.tangentSpaceTensor F V))
