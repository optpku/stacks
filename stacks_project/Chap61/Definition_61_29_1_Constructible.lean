/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.Constructible

/-! Source-facing bridge for constructible pro-étale derived objects. -/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived

universe u v

#check @AlgebraicGeometry.Scheme.ProetaleDerived.locallyHasFiniteTorDimension
#check @AlgebraicGeometry.Scheme.ProetaleDerived.locallyHasFiniteTorDimension_iff
#check (AlgebraicGeometry.Scheme.ProetaleDerived.IsConstructible :
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
#check @AlgebraicGeometry.Scheme.ProetaleDerived.isConstructible_iff
#check @AlgebraicGeometry.Scheme.ProetaleDerived.IsConstructible.spec
#check @AlgebraicGeometry.Scheme.ProetaleDerived.instIsConstructible_zero
#check @AlgebraicGeometry.Scheme.ProetaleDerived.constructibleObjectProperty
#check @AlgebraicGeometry.Scheme.ProetaleDerived.constructibleObjectProperty_apply
#check @AlgebraicGeometry.Scheme.ProetaleDerived.ProetaleConstructible
#check @AlgebraicGeometry.Scheme.ProetaleDerived.ProetaleConstructible.mk
#check @AlgebraicGeometry.Scheme.ProetaleDerived.ProetaleConstructible.mem_iff
