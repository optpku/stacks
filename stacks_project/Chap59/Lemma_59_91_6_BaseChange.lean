module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Injective

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

#check (AlgebraicGeometry.Scheme.Hom.abelianPullbackAlong :
  ∀ {A B : Scheme.{u}} (morphism : A ⟶ B),
    Sheaf B.smallEtaleTopology AddCommGrpCat.{u} →
      Sheaf A.smallEtaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Hom.abelianPushforwardAlong :
  ∀ {A B : Scheme.{u}} (morphism : A ⟶ B),
    Sheaf A.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Hom.etaleAbelianSheafPullback_comp :
  ∀ {A B C : Scheme.{u}} (first : B ⟶ A) (second : C ⟶ B),
    etaleAbelianSheafPullback first ⋙ etaleAbelianSheafPullback second ≅
      etaleAbelianSheafPullback (second ≫ first))

#check (AlgebraicGeometry.Scheme.Hom.etaleAbelianSheafPullback_square :
  ∀ (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X),
    IsPullback g' f' f g →
      (etaleAbelianSheafPullback g ⋙ etaleAbelianSheafPullback f' ≅
        etaleAbelianSheafPullback f ⋙ etaleAbelianSheafPullback g'))

#check (AlgebraicGeometry.Scheme.Hom.underivedBaseChange :
  ∀ (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X),
    IsPullback g' f' f g →
      (abelianPushforwardAlong f ⋙ etaleAbelianSheafPullback g ⟶
        etaleAbelianSheafPullback g' ⋙ abelianPushforwardAlong f'))

#check (AlgebraicGeometry.Scheme.Hom.higherDirectImage_baseChangeHom :
  ∀ (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X),
    IsPullback g' f' f g →
      ∀ (sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (degree : ℕ),
        ((abelianPushforwardAlong f ⋙ etaleAbelianSheafPullback g).rightDerived degree).obj
            sheaf ⟶
          ((etaleAbelianSheafPullback g' ⋙ abelianPushforwardAlong f').rightDerived degree).obj
            sheaf)

#check (AlgebraicGeometry.Scheme.Hom.higherDirectImage_baseChangeHom_eq :
  ∀ (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (degree : ℕ),
    higherDirectImage_baseChangeHom f g f' g' h_cart sheaf degree =
      (NatTrans.rightDerived (underivedBaseChange f g f' g' h_cart) degree).app sheaf)

#check (AlgebraicGeometry.Scheme.Hom.higherDirectImageBaseChange :
  ∀ (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X),
    IsPullback g' f' f g →
      ∀ (sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (degree : ℕ),
        abelianPullbackAlong g (schemeHigherDirectImage f sheaf degree) ⟶
          schemeHigherDirectImage f' (abelianPullbackAlong g' sheaf) degree)

#check (AlgebraicGeometry.Scheme.Hom.CohomologyCommutesWithBaseChange : (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Scheme.Hom.cohomologyCommutesWithBaseChange_apply :
  ∀ {f : X ⟶ Y}, CohomologyCommutesWithBaseChange f →
    ∀ {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
      (h_cart : IsPullback g' f' f g)
      {sheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}},
      IsLocallyTorsion sheaf →
        ∀ degree : ℕ, IsIso (higherDirectImageBaseChange f g f' g' h_cart sheaf degree))

#check (AlgebraicGeometry.Scheme.Hom.modSheafToAbelian :
  ∀ {X : Scheme.{u}} {modulus : ℕ},
    Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod modulus)) →
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Hom.injectiveMod_higherDirectImage_isZero : (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Scheme.Hom.injectiveMod_higherDirectImage_isZero_apply :
  ∀ {f : X ⟶ Y}, injectiveMod_higherDirectImage_isZero f →
    ∀ {modulus : ℕ}, Nat.Prime modulus →
      ∀ {sheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod modulus))},
        Injective sheaf →
          ∀ {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X},
            IsPullback g' f' f g → ∀ {degree : ℕ}, 0 < degree →
              IsZero (schemeHigherDirectImage f'
                (abelianPullbackAlong g' (modSheafToAbelian sheaf)) degree))

end AlgebraicGeometry.Scheme.Hom

end
