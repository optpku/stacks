/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.AdicConstructible
import StacksCheckRecall

/-!
# Proposition 61.29.7

On a Noetherian scheme, every constructible object of `D(X_proétale, Λ)` is
adic constructible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DerivedCategory
open CategoryTheory.Sheaf AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

/- Proposition 61.29.7: on a Noetherian scheme, every constructible pro-étale derived object
with coefficients in a Noetherian ring is adic constructible. -/
@[stacks 09C7] #check
  (AlgebraicGeometry.Scheme.ProEt.instIsAdicConstructible_of_isConstructible :
    ∀ {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
      [∀ {Y : Scheme.{u}}, HasSheafify (topology Y) (ModuleCat.{w} Λ)]
      [∀ {Y : Scheme.{u}}, HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))]
      [HasWeakSheafify (topology X) CommRingCat.{w}]
      [HasWeakSheafify (topology X) RingCat.{w}]
      [HasWeakSheafify (topology X) AddCommGrpCat.{w}]
      [(topology X).WEqualsLocallyBijective RingCat.{w}]
      [(topology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
      [(topology X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
      [(topology X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
      [(topology X).PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
      [UnivLE.{u + 1, w}]
      [LocallySmall
        (SheafOfModules (ringSheafOfComm (ProetaleDerived.constantCoefficientRing X Λ)))]
      [WellPowered
        (SheafOfModules (ringSheafOfComm (ProetaleDerived.constantCoefficientRing X Λ)))]
      [∀ U : X.ProEt,
        ((ProEt.topology X).over U).HasSheafCompose
          (forget₂ CommRingCat.{w} RingCat.{w})]
      [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{w}]
      [∀ U : X.ProEt,
        ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
      [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
        (baseChange f).op.HasLeftKanExtension P]
      [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
      [∀ {Y : Scheme.{u}} (U : Y.ProEt),
        Abelian (Sheaf ((topology Y).over U) (ModuleCat.{w} Λ))]
      [∀ {Y : Scheme.{u}} (U : Y.ProEt),
        HasDerivedCategory (Sheaf ((topology Y).over U) (ModuleCat.{w} Λ))]
      [∀ {Y : Scheme.{u}} (U : Y.ProEt),
        ((topology Y).overPullback (ModuleCat.{w} Λ) U).Additive]
      [∀ {Y : Scheme.{u}} (U : Y.ProEt),
        PreservesFiniteLimits ((topology Y).overPullback (ModuleCat.{w} Λ) U)]
      [∀ {Y : Scheme.{u}} (U : Y.ProEt),
        PreservesFiniteColimits ((topology Y).overPullback (ModuleCat.{w} Λ) U)]
      [∀ {Y : Scheme.{u}}, HasTerminal Y.ProEt]
      (I : Ideal Λ)
      [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
      [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))))]
      [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X).Additive]
      [(Functor.Homotopy.toDerived
          (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (ComplexShape.up ℤ))]
      [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))),
        (ProEt.baseChange f).op.HasLeftKanExtension P]
      [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
      [∀ {Y : Scheme.{u}} (U : Y.ProEt),
        HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
      (K : ProetaleDerived X Λ)
      [IsNoetherian X] [ProetaleDerived.IsConstructible I K],
    Derived.IsAdicConstructible I K)

end AlgebraicGeometry.Scheme.ProEt

end
