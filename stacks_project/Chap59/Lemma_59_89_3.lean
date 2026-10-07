module

public import stacks_project.Chap59.Lemma_59_91_12_BaseChange
public import stacks_project.Chap59.Theorem_59_89_2_Smooth_base_change
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
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

/-- Lemma 59.89.3: if `S' = lim S_i` is a directed inverse limit of schemes
smooth over `S` with affine transition morphisms, and `f : X ⟶ S` is
quasi-compact and quasi-separated, then for a cartesian fibre square with
projections `f' : X' ⟶ S'` and `g' : X' ⟶ X`, the canonical derived
base-change map `g⁻¹ Rf_* E ⟶ R(f')_* (g')⁻¹ E` is an isomorphism for every
`E ∈ D⁺(X_étale)` whose cohomology sheaves have geometric stalks that are
torsion of orders invertible on `S`. -/
@[stacks 0F09]
theorem derivedBaseChange_isIso_of_smoothInverseLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (DS : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S)
    [∀ i : I, Smooth (gi i)]
    (hgi : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j)
    (cS : Cone DS) (hcS : IsLimit cS) (g : cS.pt ⟶ S)
    (hg : ∀ i : I, cS.π.app (OrderDual.toDual i) ≫ gi i = g)
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {X' : Scheme.{u}} (f' : X' ⟶ cS.pt) (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g').obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact g').obj ⋙ abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison f g))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn S :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E) :
    IsIso (derivedBaseChangeHom f g f' g' h_cart h_src E) := sorry

/-- Specialization of `derivedBaseChange_isIso_of_smoothInverseLimit` to the
chosen fibre product `S' ×_S X`, with projections `f' = pullback.fst g f`
and `g' = pullback.snd g f`. -/
theorem derivedBaseChange_isIso_of_smoothInverseLimit_pullback
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (DS : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S)
    [∀ i : I, Smooth (gi i)]
    (hgi : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j)
    (cS : Cone DS) (hcS : IsLimit cS) (g : cS.pt ⟶ S)
    (hg : ∀ i : I, cS.π.app (OrderDual.toDual i) ≫ gi i = g)
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [HasPullback g f]
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong (pullback.fst g f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (pullback g f).smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}))]
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
      (IsTorsionWithOrdersInvertibleOn S :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E) :
    IsIso
      (derivedBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
        (IsPullback.of_hasPullback g f).flip h_src E) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
