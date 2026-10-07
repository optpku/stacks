module

public import stacks_project.Chap59.Lemma_59_91_12_BaseChange
public import stacks_project.Chap59.Theorem_59_89_2_Smooth_base_change
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
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

/-- Lemma 59.97.5: if `K` is a field, `j : U ⟶ X` is an open immersion of schemes of
finite type over `K`, and `Y` is a scheme of finite type over `K`, then for
`q = pullback.snd Y.hom X.hom : pullback Y.hom X.hom ⟶ X.left`,
`h = pullback.fst q j.left`, and `p = pullback.snd q j.left`, the derived
base-change map `q⁻¹ R j_* F ⟶ R h_* p⁻¹ F` is an isomorphism for every abelian
sheaf `F` on `U.left.smallEtaleTopology` whose geometric stalks are torsion of
orders invertible in `K`. -/
@[stacks 0F1H]
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

end AlgebraicGeometry.Scheme.Hom

end

end
