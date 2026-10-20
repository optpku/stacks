module

public import stacks_project.Chap61.Definition_61_29_1_Derived
public import stacks_project.Chap61.Definition_61_29_1_Constructible
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.ProperBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived
open RingedSite.Hom
open scoped ZeroObject

noncomputable section

universe u v

/- Definition 61.29.1 (1): an object `K` of `D(X_proétale, Λ)` is constructible when it is
  derived complete with respect to `I` and its reduction has constructible cohomology sheaves
  and locally finite Tor dimension. -/
@[stacks 09C1] #check (AlgebraicGeometry.Scheme.ProetaleDerived.IsConstructible :
  ∀ {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
    [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) RingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{v}]
    [(ProEt.topology X).WEqualsLocallyBijective RingCat.{v}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
    [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
    [UnivLE.{u + 1, v}]
    [LocallySmall
      (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
    [WellPowered
      (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
    [∀ U : X.ProEt,
      ((ProEt.topology X).over U).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{v}]
    [∀ U : X.ProEt,
      ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{v} Λ)]
    (I : Ideal Λ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
      (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (ComplexShape.up ℤ))]
    [∀ U : X.ProEt, @DerivedTensor.Right.Has
      (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, v, v}
        ((ProEt.topology X).over U)
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory
        ((ProEt.topology X).over U)
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
      (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [∀ {Y : Scheme.{u}},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))]
    [∀ {Y : Scheme.{u}} (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))],
    (X.ProetaleDerived Λ → Prop))

/- Definition 61.29.1 (2): `D_cons(X, Λ)` is the full subcategory of constructible objects
  in `D(X_proétale, Λ)`. -/
@[stacks 09C1] #check (AlgebraicGeometry.Scheme.ProetaleDerived.ProetaleConstructible :
  ∀ (X : Scheme.{u}) {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
    [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) RingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{v}]
    [(ProEt.topology X).WEqualsLocallyBijective RingCat.{v}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
    [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
    [UnivLE.{u + 1, v}]
    [LocallySmall
      (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
    [WellPowered
      (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
    [∀ U : X.ProEt,
      ((ProEt.topology X).over U).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{v}]
    [∀ U : X.ProEt,
      ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{v} Λ)]
    (I : Ideal Λ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
      (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (ComplexShape.up ℤ))]
    [∀ U : X.ProEt, @DerivedTensor.Right.Has
      (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, v, v}
        ((ProEt.topology X).over U)
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory
        ((ProEt.topology X).over U)
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
      (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [∀ {Y : Scheme.{u}},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))]
    [∀ {Y : Scheme.{u}} (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))],
    Type (max (u + 1) (v + 1)))
