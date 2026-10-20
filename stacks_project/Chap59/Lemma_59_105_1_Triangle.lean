module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Etale.Comparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

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

/- The canonical étale derived comparisons of a blow-up square commute. -/
#check (AlgebraicGeometry.IsBlowup.Etale.square :
  ∀ (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})),
    CommSq (toCenter I b K) (toBlowup I b K)
      (centerToExceptional I b K) (blowupToExceptional I b K))

end AlgebraicGeometry.IsBlowup.Etale

end

end
