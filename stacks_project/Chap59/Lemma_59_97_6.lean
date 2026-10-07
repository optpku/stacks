module

public import stacks_project.Chap59.Lemma_59_91_12_BaseChange
public import stacks_project.Chap59.Theorem_59_89_2_Smooth_base_change
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 59.97.6: if `K` is a field, `x : X ⟶ Spec (CommRingCat.of K)` and
`s : S' ⟶ Spec (CommRingCat.of K)` are structure morphisms, the squares
`IsPullback p f' x s` and `IsPullback h e f' g` are cartesian, and
`g : T ⟶ S'` is quasi-compact and quasi-separated, then for every abelian sheaf
`F` on `T.smallEtaleTopology` whose geometric stalks are torsion of orders
invertible in `K`, the derived étale base-change map
`(f')⁻¹ R g_* F ⟶ R h_* e⁻¹ F` is an isomorphism. The comparison is
`derivedBaseChangeHom g f' h e h_right.flip h_src` applied to `F` placed in
degree `0`. -/
@[stacks 0F1I]
theorem derivedBaseChangeHom_isIso_of_qcqs_overField
    {K : Type u} [Field K] {X S' T X' Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (s : S' ⟶ Spec (CommRingCat.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    [QuasiCompact g] [QuasiSeparated g]
    [(abelianPushforwardAlong g).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong h).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact f').obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact e).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong g ⋙ (etalePullbackExact f').obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact e).obj ⋙ abelianPushforwardAlong h).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_left : IsPullback p f' x s) (h_right : IsPullback h e f' g)
    (h_src : IsIso (derivedSourceComparison g f'))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of K)) F) :
    IsIso (derivedBaseChangeHom g f' h e h_right.flip h_src
      ((DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) 0).obj F)) := sorry

/-- Specialization of `derivedBaseChangeHom_isIso_of_qcqs_overField` to the chosen
fibre products `pullback x s` and `pullback (pullback.snd x s) g`, with
`f' = pullback.snd x s`, `h = pullback.fst (pullback.snd x s) g`, and
`e = pullback.snd (pullback.snd x s) g`. -/
theorem derivedBaseChangeHom_isIso_of_qcqs_overField_pullback
    {K : Type u} [Field K] {X S' T : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (s : S' ⟶ Spec (CommRingCat.of K))
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    [HasPullback x s] [HasPullback (pullback.snd x s) g]
    [(abelianPushforwardAlong g).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong (pullback.fst (pullback.snd x s) g)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact (pullback.snd x s)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact (pullback.snd (pullback.snd x s) g)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong g ⋙
        (etalePullbackExact (pullback.snd x s)).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact (pullback.snd (pullback.snd x s) g)).obj ⋙
        abelianPushforwardAlong
          (pullback.fst (pullback.snd x s) g)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison g (pullback.snd x s)))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of K)) F) :
    IsIso (derivedBaseChangeHom g (pullback.snd x s)
      (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
      (IsPullback.of_hasPullback (pullback.snd x s) g).flip h_src
      ((DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) 0).obj F)) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
