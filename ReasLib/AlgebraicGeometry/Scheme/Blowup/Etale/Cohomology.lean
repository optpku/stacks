/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Etale.Triangle
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.BoundedBelow.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.BoundedBelow.Basic
public import Mathlib.Algebra.Homology.ExactSequence

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.ComposableArrows
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived.Bounded

noncomputable section

universe w u

namespace AlgebraicGeometry.IsBlowup.Etale

variable {X X' : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
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

/-- Restriction to the center and to the blow-up gives a map to their hypercohomology
biproduct, with the center as the first summand. -/
def cohomologyToBiprod (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    (Scheme.Etale.BoundedBelow.hypercohomologyFunctor X p).obj K ⟶
      (Scheme.Etale.BoundedBelow.hypercohomologyFunctor I.subscheme p).obj
          ((etaleDerivedInverseImage I.subschemeι).obj K) ⊞
        (Scheme.Etale.BoundedBelow.hypercohomologyFunctor X' p).obj
          ((etaleDerivedInverseImage b).obj K) :=
  biprod.lift
    (derivedEtaleCohomologyRestrict I.subschemeι K p)
    (derivedEtaleCohomologyRestrict b K p)

/-- The map to the center-first biproduct is the lift of the two canonical restrictions. -/
theorem cohomologyToBiprod_eq (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    cohomologyToBiprod I b K p =
      biprod.lift
        (derivedEtaleCohomologyRestrict I.subschemeι K p)
        (derivedEtaleCohomologyRestrict b K p) := rfl

/-- From the center-first hypercohomology biproduct, take restriction from the center
minus restriction from the blow-up to the exceptional scheme. The inverse-image composition
isomorphisms identify both targets with restriction along the composite to the base scheme. -/
def cohomologyDifference (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    (Scheme.Etale.BoundedBelow.hypercohomologyFunctor I.subscheme p).obj
        ((etaleDerivedInverseImage I.subschemeι).obj K) ⊞
      (Scheme.Etale.BoundedBelow.hypercohomologyFunctor X' p).obj
        ((etaleDerivedInverseImage b).obj K) ⟶
    (Scheme.Etale.BoundedBelow.hypercohomologyFunctor (I.comap b).subscheme p).obj
      ((etaleDerivedInverseImage (composite I b)).obj K) :=
  biprod.desc
    (derivedEtaleCohomologyRestrict (exceptionalProjection I b)
        ((etaleDerivedInverseImage I.subschemeι).obj K) p ≫
      (Scheme.Etale.BoundedBelow.hypercohomologyFunctor (I.comap b).subscheme p).map
        ((inverseImageCompIso I.subschemeι (exceptionalProjection I b)).hom.app K))
    (-(derivedEtaleCohomologyRestrict (I.comap b).subschemeι
          ((etaleDerivedInverseImage b).obj K) p ≫
        (Scheme.Etale.BoundedBelow.hypercohomologyFunctor (I.comap b).subscheme p).map
          ((inverseImageCompIso b (I.comap b).subschemeι ≪≫
              composite_inverseImageIso I b).hom.app K)))

/-- The difference map is the signed biproduct desc of the exceptional restrictions,
transported along the inverse-image composition isomorphisms. -/
theorem cohomologyDifference_eq (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    cohomologyDifference I b K p =
      (show
        (Scheme.Etale.BoundedBelow.hypercohomologyFunctor I.subscheme p).obj
            ((etaleDerivedInverseImage I.subschemeι).obj K) ⊞
          (Scheme.Etale.BoundedBelow.hypercohomologyFunctor X' p).obj
            ((etaleDerivedInverseImage b).obj K) ⟶
        (Scheme.Etale.BoundedBelow.hypercohomologyFunctor (I.comap b).subscheme p).obj
          ((etaleDerivedInverseImage (composite I b)).obj K) from
        biprod.desc
          (derivedEtaleCohomologyRestrict (exceptionalProjection I b)
              ((etaleDerivedInverseImage I.subschemeι).obj K) p ≫
            (Scheme.Etale.BoundedBelow.hypercohomologyFunctor (I.comap b).subscheme p).map
              ((inverseImageCompIso I.subschemeι (exceptionalProjection I b)).hom.app K))
          (-(derivedEtaleCohomologyRestrict (I.comap b).subschemeι
                ((etaleDerivedInverseImage b).obj K) p ≫
              (Scheme.Etale.BoundedBelow.hypercohomologyFunctor (I.comap b).subscheme p).map
                ((inverseImageCompIso b (I.comap b).subschemeι ≪≫
                    composite_inverseImageIso I b).hom.app K)))) := by
  unfold cohomologyDifference
  rfl

/-- A blow-up along a finite-type quasi-coherent ideal induces a long exact sequence
of étale hypercohomology, with connecting maps natural in bounded-below coefficients
having locally torsion cohomology sheaves. The biproduct is ordered center first, then
blow-up, and the next map is center restriction minus blow-up restriction. Swapping
the summands gives the blow-up-first convention with the corresponding sign change. -/
theorem cohomologySequence_exact {I : X.IdealSheafData} {b : X' ⟶ X} [IsBlowup b I]
    (hI : I.IsFiniteType) :
    let P := DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    let J := P.ι
    let E := (I.comap b).subscheme
    let c := composite I b
    ∃ δ : ∀ p : ℤ,
      (J ⋙ etaleDerivedInverseImage c ⋙
          Scheme.Etale.BoundedBelow.hypercohomologyFunctor E p) ⟶
        (J ⋙ Scheme.Etale.BoundedBelow.hypercohomologyFunctor X (p + 1)),
      ∀ (K : P.FullSubcategory) (p : ℤ),
        (mk₄ (cohomologyToBiprod I b K.obj p) (cohomologyDifference I b K.obj p)
          ((δ p).app K) (cohomologyToBiprod I b K.obj (p + 1))).Exact := sorry

end AlgebraicGeometry.IsBlowup.Etale

end

end
