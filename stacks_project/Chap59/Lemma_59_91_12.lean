/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_12_BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
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

/-- Lemma 59.91.12: if `f : X ⟶ Y` is a proper morphism of schemes, `g : Y' ⟶ Y` is
any morphism of schemes, `X'` is cartesian over `Y` with projections `f'` and `g'`,
and `E ∈ D⁺(X_étale)` has locally torsion cohomology sheaves, then the canonical
base-change map `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism. -/
@[stacks 0DDE]
theorem derivedBaseChange_isIso_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g').obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact g').obj ⋙ abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison f g))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E) :
    IsIso (derivedBaseChangeHom f g f' g' h_cart h_src E) := sorry

/-- Specialization of `derivedBaseChange_isIso_of_isProper` to the chosen fibre product
`Y' ×_Y X`, with projections `f' = pullback.fst g f` and `g' = pullback.snd g f`. -/
theorem derivedBaseChange_isIso_of_isProper_pullback
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y)
    [HasPullback g f]
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong (pullback.fst g f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (pullback g f).smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact (pullback.snd g f)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact (pullback.snd g f)).obj ⋙
        abelianPushforwardAlong (pullback.fst g f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison f g))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E) :
    IsIso
      (derivedBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
        (IsPullback.of_hasPullback g f).flip h_src E) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
