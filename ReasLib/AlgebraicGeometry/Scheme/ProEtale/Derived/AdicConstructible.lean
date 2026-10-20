/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedAdicSheaf

/-!
# Constructible derived objects are adic constructible

On a Noetherian scheme, every constructible object of `D(X_proétale, Λ)` is
adic constructible.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ {Y : Scheme.{u}}, HasSheafify (topology Y) (ModuleCat.{w} Λ)]

/-- Abelian structure on pro-étale module sheaves, uniformly in the scheme. -/
instance instAbelian_forall_proEtModuleSheaf :
    ∀ {Y : Scheme.{u}}, Abelian (Sheaf (topology Y) (ModuleCat.{w} Λ)) :=
  fun {_} ↦ inferInstance

variable [∀ {Y : Scheme.{u}}, HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))]
variable [HasWeakSheafify (topology X) CommRingCat.{w}]
variable [HasWeakSheafify (topology X) RingCat.{w}]
variable [HasWeakSheafify (topology X) AddCommGrpCat.{w}]
variable [(topology X).WEqualsLocallyBijective RingCat.{w}]
variable [(topology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [(topology X).PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{u + 1, w}]
variable [LocallySmall
  (SheafOfModules (ringSheafOfComm (ProetaleDerived.constantCoefficientRing X Λ)))]
variable [WellPowered
  (SheafOfModules (ringSheafOfComm (ProetaleDerived.constantCoefficientRing X Λ)))]

-- Tor tests on slices use the actual constant-coefficient structure-ring tensor.
variable [∀ U : X.ProEt,
  ((ProEt.topology X).over U).HasSheafCompose
    (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{w}]
variable [∀ U : X.ProEt,
  ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  Abelian (Sheaf ((topology Y).over U) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasDerivedCategory (Sheaf ((topology Y).over U) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  ((topology Y).overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  PreservesFiniteLimits ((topology Y).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  PreservesFiniteColimits ((topology Y).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ {Y : Scheme.{u}}, HasTerminal Y.ProEt]

variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))))]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (ComplexShape.up ℤ))]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))),
  (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]

variable (K : ProetaleDerived X Λ)

/-- Every constructible pro-étale derived object on a Noetherian scheme with coefficients
in a Noetherian ring is adic constructible with respect to the coefficient ideal. -/
instance instIsAdicConstructible_of_isConstructible
    [IsNoetherian X] [ProetaleDerived.IsConstructible I K] :
    Derived.IsAdicConstructible I K :=
  sorry

end AlgebraicGeometry.Scheme.ProEt

end
