/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import stacks_project.Chap59.Lemma_59_105_1
public import stacks_project.Chap59.Lemma_59_90_2_Restrict
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.ComposableArrows
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.IsBlowup.Etale
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open CategoryTheory.Functor.RightDerived.Bounded

noncomputable section

universe w u

namespace AlgebraicGeometry.IsBlowup.Etale

variable {X X' : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (p : A ⟶ B),
    (abelianPushforwardAlong p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))]
variable [∀ {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C),
    (abelianPushforwardAlong f ⋙ abelianPushforwardAlong g).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))]
variable [∀ Z : Scheme.{u},
    ((siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}))]
variable [∀ {A B : Scheme.{u}} (p : A ⟶ B),
    (etaleAbelianSheafPullback p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf B.smallEtaleTopology AddCommGrpCat.{u}))]
variable [∀ {A B : Scheme.{u}} (p : A ⟶ B),
    (etaleAbelianSheafPullback p ⋙
        siteAbelianSectionsFunctor A.smallEtaleTopology (globalEtale A)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf B.smallEtaleTopology AddCommGrpCat.{u}))]

/-- The first map of the blow-up étale hypercohomology sequence, as the biproduct lift of
restriction along the center immersion and along the blow-up morphism. -/
noncomputable def cohomologyToBiprod (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).obj
      ((functor (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X))).obj K) ⟶
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).obj
        ((functor
            (siteAbelianSectionsFunctor I.subscheme.smallEtaleTopology
              (globalEtale I.subscheme))).obj
          ((etaleDerivedInverseImage I.subschemeι).obj K)) ⊞
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).obj
        ((functor
            (siteAbelianSectionsFunctor X'.smallEtaleTopology (globalEtale X'))).obj
          ((etaleDerivedInverseImage b).obj K)) :=
  biprod.lift
    (derivedEtaleCohomologyRestrict I.subschemeι K p)
    (derivedEtaleCohomologyRestrict b K p)

/-- `cohomologyToBiprod` is the biproduct lift of `derivedEtaleCohomologyRestrict` along the
center immersion and the blow-up morphism. -/
theorem cohomologyToBiprod_eq (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    cohomologyToBiprod I b K p =
      biprod.lift
        (derivedEtaleCohomologyRestrict I.subschemeι K p)
        (derivedEtaleCohomologyRestrict b K p) := sorry

/-- The second map of the blow-up étale hypercohomology sequence, as the signed biproduct
desc of restrictions to the exceptional divisor, transported to inverse image along
`composite I b`. -/
noncomputable def cohomologyDifference (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).obj
        ((functor
            (siteAbelianSectionsFunctor I.subscheme.smallEtaleTopology
              (globalEtale I.subscheme))).obj
          ((etaleDerivedInverseImage I.subschemeι).obj K)) ⊞
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).obj
        ((functor
            (siteAbelianSectionsFunctor X'.smallEtaleTopology (globalEtale X'))).obj
          ((etaleDerivedInverseImage b).obj K)) ⟶
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).obj
      ((functor
          (siteAbelianSectionsFunctor (I.comap b).subscheme.smallEtaleTopology
            (globalEtale (I.comap b).subscheme))).obj
        ((etaleDerivedInverseImage (composite I b)).obj K)) :=
  biprod.desc
    (derivedEtaleCohomologyRestrict (exceptionalProjection I b)
        ((etaleDerivedInverseImage I.subschemeι).obj K) p ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).map
        ((functor
            (siteAbelianSectionsFunctor (I.comap b).subscheme.smallEtaleTopology
              (globalEtale (I.comap b).subscheme))).map
          ((inverseImageCompIso I.subschemeι (exceptionalProjection I b)).hom.app K)))
    (-(derivedEtaleCohomologyRestrict (I.comap b).subschemeι
          ((etaleDerivedInverseImage b).obj K) p ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).map
          ((functor
              (siteAbelianSectionsFunctor (I.comap b).subscheme.smallEtaleTopology
                (globalEtale (I.comap b).subscheme))).map
            ((inverseImageCompIso b (I.comap b).subschemeι ≪≫
                composite_inverseImageIso I b).hom.app K))))

/-- `cohomologyDifference` is the signed transported biproduct desc of restrictions along
the exceptional projection and the exceptional immersion. -/
theorem cohomologyDifference_eq (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    cohomologyDifference I b K p =
      biprod.desc
        (derivedEtaleCohomologyRestrict (exceptionalProjection I b)
            ((etaleDerivedInverseImage I.subschemeι).obj K) p ≫
          (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).map
            ((functor
                (siteAbelianSectionsFunctor (I.comap b).subscheme.smallEtaleTopology
                  (globalEtale (I.comap b).subscheme))).map
              ((inverseImageCompIso I.subschemeι (exceptionalProjection I b)).hom.app K)))
        (-(derivedEtaleCohomologyRestrict (I.comap b).subschemeι
              ((etaleDerivedInverseImage b).obj K) p ≫
            (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).map
              ((functor
                  (siteAbelianSectionsFunctor (I.comap b).subscheme.smallEtaleTopology
                    (globalEtale (I.comap b).subscheme))).map
                ((inverseImageCompIso b (I.comap b).subschemeι ≪≫
                    composite_inverseImageIso I b).hom.app K)))) := sorry

/-- Lemma 59.105.2: for a scheme `X` and `K ∈ D⁺(X_étale)` with torsion cohomology
sheaves, if `Z ⊂ X` is a closed subscheme cut out by a quasi-coherent ideal of finite
type, then the corresponding blow-up square `E ⟶ X'` over `Z ⟶ X` induces a canonical
long exact sequence of étale hypercohomology groups
`H^p_étale(X, K) ⟶ H^p_étale(Z, K|_Z) ⊞ H^p_étale(X', K|_{X'}) ⟶
H^p_étale(E, K|_E) ⟶ H^{p+1}_étale(X, K)`. The first two maps are
`cohomologyToBiprod` and `cohomologyDifference`; a connecting map exists making the
displayed four-arrow sequence exact at the biproduct, at `H^p_étale(E, K|_E)`, and at
`H^{p+1}_étale(X, K)`. The source writes the middle summand as
`H^p_étale(X', K|_{X'}) ⊕ H^p_étale(Z, K|_Z)`; the API follows the `(Z, X')` order of
`(square I b K).shortComplex'`. -/
@[stacks 0EW3]
theorem cohomologySequence_exact {I : X.IdealSheafData} {b : X' ⟶ X} [IsBlowup b I]
    (hI : I.IsFiniteType)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) K)
    (p : ℤ) :
    ∃ δ :
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).obj
          ((functor
              (siteAbelianSectionsFunctor (I.comap b).subscheme.smallEtaleTopology
                (globalEtale (I.comap b).subscheme))).obj
            ((etaleDerivedInverseImage (composite I b)).obj K)) ⟶
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (p + 1)).obj
          ((functor
              (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X))).obj K),
      (mk₄ (cohomologyToBiprod I b K p) (cohomologyDifference I b K p) δ
          (cohomologyToBiprod I b K (p + 1))).Exact := sorry

end AlgebraicGeometry.IsBlowup.Etale

end

end
