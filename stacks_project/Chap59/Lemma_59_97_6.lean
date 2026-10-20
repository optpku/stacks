module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.OverField
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

/- Lemma 59.97.6: if `K` is a field, `x : X ⟶ Spec (CommRingCat.of K)` and
`s : S' ⟶ Spec (CommRingCat.of K)` are structure morphisms, the squares
`IsPullback p f' x s` and `IsPullback h e f' g` are cartesian, and
`g : T ⟶ S'` is quasi-compact and quasi-separated, then for every abelian sheaf
`F` on `T.smallEtaleTopology` whose geometric stalks are torsion of orders
invertible in `K`, the derived étale base-change map
`(f')⁻¹ R g_* F ⟶ R h_* e⁻¹ F` is an isomorphism. -/
@[stacks 0F1I] #check
  (AlgebraicGeometry.Scheme.Hom.derivedBaseChangeHom_isIso_of_qcqs_overField :
    ∀ {K : Type u} [Field K] {X S' T X' Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (s : S' ⟶ Spec (CommRingCat.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    [QuasiCompact g] [QuasiSeparated g]
    (h_left : IsPullback p f' x s) (h_right : IsPullback h e f' g)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionWithOrdersInvertibleOn.{u, u + 1} (Spec (CommRingCat.of K)) F),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMapOfCommSq
      g f' h e h_right.flip.toCommSq
      ((DerivedCategory.singleFunctor
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))

#check
  (AlgebraicGeometry.Scheme.Hom.derivedBaseChangeHom_isIso_of_qcqs_overField_pullback :
    ∀ {K : Type u} [Field K] {X S' T : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (s : S' ⟶ Spec (CommRingCat.of K))
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    [HasPullback x s] [HasPullback (pullback.snd x s) g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionWithOrdersInvertibleOn.{u, u + 1} (Spec (CommRingCat.of K)) F),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMapOfCommSq
      g (pullback.snd x s)
      (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
      (IsPullback.of_hasPullback (pullback.snd x s) g).flip.toCommSq
      ((DerivedCategory.singleFunctor
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))

end

end
