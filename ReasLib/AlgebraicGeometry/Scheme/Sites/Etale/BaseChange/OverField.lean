/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Torsion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Derived étale pushforward along a quasi-compact, quasi-separated morphism
commutes with base change by a scheme over a field for abelian sheaves whose
geometric stalks are torsion of orders invertible in the field. -/
theorem derivedBaseChangeHom_isIso_of_qcqs_overField
    {K : Type u} [Field K] {X S' T X' Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (s : S' ⟶ Spec (CommRingCat.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    [QuasiCompact g] [QuasiSeparated g]
    (h_left : IsPullback p f' x s) (h_right : IsPullback h e f' g)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionWithOrdersInvertibleOn.{u, u + 1} (Spec (CommRingCat.of K)) F) :
    IsIso (BaseChange.derivedMapOfCommSq g f' h e h_right.flip.toCommSq
      ((DerivedCategory.singleFunctor
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) := sorry

/-- For the chosen fibre products with a scheme over a field, the canonical
derived étale base-change map for a quasi-compact, quasi-separated morphism is
an isomorphism on abelian sheaves whose geometric stalks are torsion of orders
invertible in the field. -/
theorem derivedBaseChangeHom_isIso_of_qcqs_overField_pullback
    {K : Type u} [Field K] {X S' T : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (s : S' ⟶ Spec (CommRingCat.of K))
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    [HasPullback x s] [HasPullback (pullback.snd x s) g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionWithOrdersInvertibleOn.{u, u + 1} (Spec (CommRingCat.of K)) F) :
    IsIso (BaseChange.derivedMapOfCommSq g (pullback.snd x s)
      (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
      (IsPullback.of_hasPullback (pullback.snd x s) g).flip.toCommSq
      ((DerivedCategory.singleFunctor
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) :=
  derivedBaseChangeHom_isIso_of_qcqs_overField x s (pullback.fst x s)
    (pullback.snd x s) g (pullback.fst (pullback.snd x s) g)
    (pullback.snd (pullback.snd x s) g) (IsPullback.of_hasPullback x s)
    (IsPullback.of_hasPullback (pullback.snd x s) g) F hF

end AlgebraicGeometry.Scheme.Hom

end
