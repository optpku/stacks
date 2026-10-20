/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.WeaklyContractibleCover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 61.13.5 (1): the pro-étale site Sch_proétale has, for any object U,
a covering {V ⟶ U} with V a weakly contractible object. -/
@[stacks 0F4P] #check (AlgebraicGeometry.Scheme.Proetale.exists_singleton_mem_proetalePrecoverage :
  ∀ (U : Scheme.{u}), ∃ (V : Scheme.{u}) (f : V ⟶ U),
    (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
        Scheme.proetalePrecoverage U ∧
      Scheme.proetaleTopology.IsWeaklyContractible V)

/- Lemma 61.13.5 (2): the pro-étale site S_proétale has, for any object U,
a covering {V ⟶ U} with V a weakly contractible object. -/
@[stacks 0F4P] #check (AlgebraicGeometry.Scheme.ProEt.exists_singleton_mem_precoverage :
  ∀ (S : Scheme.{u}) (U : S.ProEt), ∃ (V : S.ProEt) (f : V ⟶ U),
    (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
        Scheme.ProEt.precoverage S U ∧
      (Scheme.ProEt.topology S).IsWeaklyContractible V)

/- Lemma 61.13.5 (3): the pro-étale site (Sch/S)_proétale has, for any object U,
a covering {V ⟶ U} with V a weakly contractible object. -/
@[stacks 0F4P] #check (AlgebraicGeometry.Scheme.Proetale.exists_singleton_mem_proetalePrecoverage_over :
  ∀ (S : Scheme.{u}) (U : Over S), ∃ (V : Over S) (f : V ⟶ U),
    (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
        (Scheme.proetalePrecoverage.comap (CategoryTheory.Over.forget S)) U ∧
      (Scheme.proetaleTopology.over S).IsWeaklyContractible V)

/- Lemma 61.13.5 (4): if U is quasi-compact in Sch_proétale, the covering object
V may be chosen affine and weakly contractible. -/
@[stacks 0F4P] #check (AlgebraicGeometry.Scheme.Proetale.exists_singleton_mem_proetalePrecoverage_isAffine :
  ∀ (U : Scheme.{u}) [CompactSpace U], ∃ (V : Scheme.{u}) (f : V ⟶ U),
    (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
        Scheme.proetalePrecoverage U ∧
      IsAffine V ∧ Scheme.proetaleTopology.IsWeaklyContractible V)

/- Lemma 61.13.5 (5): if U is quasi-compact in S_proétale, the covering object
V may be chosen affine and weakly contractible. -/
@[stacks 0F4P] #check (AlgebraicGeometry.Scheme.ProEt.exists_singleton_mem_precoverage_isAffine :
  ∀ (S : Scheme.{u}) (U : S.ProEt) [CompactSpace U.left],
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          Scheme.ProEt.precoverage S U ∧
        IsAffine V.left ∧ (Scheme.ProEt.topology S).IsWeaklyContractible V)

/- Lemma 61.13.5 (6): if U is quasi-compact in (Sch/S)_proétale, the covering
object V may be chosen affine and weakly contractible. -/
@[stacks 0F4P] #check (AlgebraicGeometry.Scheme.Proetale.exists_singleton_mem_proetalePrecoverage_isAffine_over :
  ∀ (S : Scheme.{u}) (U : Over S) [CompactSpace U.left],
    ∃ (V : Over S) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          (Scheme.proetalePrecoverage.comap (CategoryTheory.Over.forget S)) U ∧
        IsAffine V.left ∧ (Scheme.proetaleTopology.over S).IsWeaklyContractible V)
