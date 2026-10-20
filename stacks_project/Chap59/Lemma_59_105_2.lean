module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Etale.Cohomology
import StacksCheckRecall

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

/- Lemma 59.105.2: a blow-up square along a finite-type quasi-coherent ideal yields
 a canonical long exact sequence of étale hypercohomology for bounded-below complexes
 with torsion cohomology sheaves, natural in the coefficient complex and exact in every
 integer degree. The middle biproduct is ordered center first, then blow-up; the map
 to the exceptional term is center restriction minus blow-up restriction. This is the
 displayed blow-up-first sequence after the canonical biproduct swap and sign change. -/
@[stacks 0EW3] #check (AlgebraicGeometry.IsBlowup.Etale.cohomologySequence_exact :
  ∀ {I : X.IdealSheafData} {b : X' ⟶ X} [IsBlowup b I]
    (hI : I.IsFiniteType),
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
          ((δ p).app K) (cohomologyToBiprod I b K.obj (p + 1))).Exact)

end AlgebraicGeometry.IsBlowup.Etale

end

end
