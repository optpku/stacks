module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.BoundedBelow
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

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

/-- For an open immersion of schemes of finite type over a field, derived étale
pushforward commutes with base change by a scheme of finite type over that field
on abelian sheaves whose geometric stalks are torsion of orders invertible in
the field. -/
theorem derivedBaseChangeHom_isIso_of_openImmersion
    {K : Type u} [Field K] {X U Y : SchemeOverField K}
    [Algebraic X] [Algebraic U] [Algebraic Y]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    [HasPullback Y.hom X.hom]
    [HasPullback (pullback.snd Y.hom X.hom) j.left]
    [(abelianPushforwardAlong j.left).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong
        (pullback.fst (pullback.snd Y.hom X.hom) j.left)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (pullback (pullback.snd Y.hom X.hom) j.left).smallEtaleTopology
          AddCommGrpCat.{u}))]
    [(etalePullbackExact (pullback.snd Y.hom X.hom)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact
        (pullback.snd (pullback.snd Y.hom X.hom) j.left)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong j.left ⋙
        (etalePullbackExact (pullback.snd Y.hom X.hom)).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact
          (pullback.snd (pullback.snd Y.hom X.hom) j.left)).obj ⋙
        abelianPushforwardAlong
          (pullback.fst (pullback.snd Y.hom X.hom) j.left)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison j.left (pullback.snd Y.hom X.hom)))
    (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of K)) F) :
    IsIso
      (derivedBaseChangeHom j.left (pullback.snd Y.hom X.hom)
        (pullback.fst (pullback.snd Y.hom X.hom) j.left)
        (pullback.snd (pullback.snd Y.hom X.hom) j.left)
        (IsPullback.of_hasPullback (pullback.snd Y.hom X.hom) j.left).flip h_src
        ((DerivedCategory.Plus.singleFunctor
            (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}) 0).obj F)) := sorry

/-- Derived étale base change for an open immersion of finite-type schemes over
a field is an isomorphism when the invertible-order torsion condition on the
abelian sheaf is supplied by `Fact`. -/
instance derivedBaseChangeHom_isIso_of_openImmersion_of_fact
    {K : Type u} [Field K] {X U Y : SchemeOverField K}
    [Algebraic X] [Algebraic U] [Algebraic Y]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    [HasPullback Y.hom X.hom]
    [HasPullback (pullback.snd Y.hom X.hom) j.left]
    [(abelianPushforwardAlong j.left).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong
        (pullback.fst (pullback.snd Y.hom X.hom) j.left)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (pullback (pullback.snd Y.hom X.hom) j.left).smallEtaleTopology
          AddCommGrpCat.{u}))]
    [(etalePullbackExact (pullback.snd Y.hom X.hom)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact
        (pullback.snd (pullback.snd Y.hom X.hom) j.left)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong j.left ⋙
        (etalePullbackExact (pullback.snd Y.hom X.hom)).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact
          (pullback.snd (pullback.snd Y.hom X.hom) j.left)).obj ⋙
        abelianPushforwardAlong
          (pullback.fst (pullback.snd Y.hom X.hom) j.left)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison j.left (pullback.snd Y.hom X.hom)))
    (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u})
    [hF : Fact (IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of K)) F)] :
    IsIso
      (derivedBaseChangeHom j.left (pullback.snd Y.hom X.hom)
        (pullback.fst (pullback.snd Y.hom X.hom) j.left)
        (pullback.snd (pullback.snd Y.hom X.hom) j.left)
        (IsPullback.of_hasPullback (pullback.snd Y.hom X.hom) j.left).flip h_src
        ((DerivedCategory.Plus.singleFunctor
            (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u}) 0).obj F)) :=
  derivedBaseChangeHom_isIso_of_openImmersion j h_src F hF.out

end AlgebraicGeometry.Scheme.Hom

end

end
