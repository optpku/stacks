module

public import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry
open Algebra.FiniteType.QuasiFinite Localization.Away.Relative
open Algebra.RelativeDualizingModule
open Algebra.RelativeDualizingModule.TraceElement
open scoped Algebra.Product

universe u

/- Lemma 49.4.4: a universal trace element for a flat quasi-finite map of
Noetherian rings remains universal after Noetherian base change. -/
@[stacks 0BT9] #check
  (Algebra.RelativeDualizingModule.TraceElement.baseChange :
    ∀ (A A₁ B' B B₁' B₁ : Type u)
      [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
      [CommRing B₁'] [CommRing B₁]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [IsNoetherianRing A₁] [IsNoetherianRing B₁]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
      [IsScalarTower A₁ B₁' B₁]
      [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
      [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
      [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
      [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
      [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
      [Module.Finite A B'] [Module.Finite A₁ B₁']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
      (h_baseChange : IsBaseChange A₁
        (IsScalarTower.toAlgHom A B B₁).toLinearMap)
      (h_finiteModel : IsBaseChange A₁
        (IsScalarTower.toAlgHom A B' B₁').toLinearMap)
      (τ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open)
      (hτ : IsUniversal A B' B h_quasiFinite h_open τ),
      let h_flat₁ : Module.Flat A₁ B₁ :=
        Module.Flat.isBaseChange A A₁ B B₁ h_baseChange
      let h_quasiFinite₁ :=
        quasiFiniteOfBaseChange A A₁ B B₁ h_quasiFinite h_baseChange
      @IsUniversal A₁ B₁' B₁
        inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance h_flat₁
        h_quasiFinite₁ inferInstance h_open₁
        (baseChangeOf A A₁ B' B B₁' B₁ h_quasiFinite h_quasiFinite₁
          h_open h_open₁ h_baseChange h_finiteModel τ))

#check
  (Algebra.RelativeDualizingModule.TraceElement.awayBase :
    ∀ (A B' B : Type u)
      [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
      [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (f : A) [Algebra (Localization.Away f) B]
      [IsScalarTower A (Localization.Away f) B]
      [Module.Flat (Localization.Away f) B],
      ∀ τ,
        @IsUniversal (Localization.Away f)
          (Localization.Away (algebraMap A B' f)) B
          inferInstance inferInstance inferInstance inferInstance inferInstance
          (mapAlgebra (algebraMap A B') f)
          (awayFactorMap A B' B f).toAlgebra inferInstance
          (awayFactorMap_isScalarTower A B' B f) inferInstance
          (quasiFiniteAwayBase A B h_quasiFinite f)
          (finiteAwayBase A B' f)
          (openAwayBase A B' B h_open f) τ →
        IsUniversal A B' B h_quasiFinite h_open
          ((awayBaseIso A B' B h_quasiFinite h_open f).inv τ))

#check
  (Algebra.RelativeDualizingModule.TraceElement.awayTarget :
    ∀ (A B' B : Type u)
      [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
      [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (g : B)
      (τ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open)
      (hτ : IsUniversal A B' B h_quasiFinite h_open τ),
      IsUniversal A B' (Localization.Away g)
        (quasiFiniteAwayTarget A B h_quasiFinite g)
        (openAwayTarget B' B h_open g)
        ((awayTargetIso A B' B h_quasiFinite h_open g).hom
          (LocalizedModule.mk τ 1)))

#check
  (Algebra.RelativeDualizingModule.TraceElement.prodFst :
    ∀ (A B₁' B₁ B₂' B₂ : Type u)
      [CommRing A] [CommRing B₁'] [CommRing B₁] [CommRing B₂'] [CommRing B₂]
      [IsNoetherianRing A] [IsNoetherianRing B₁] [IsNoetherianRing B₂]
      [Algebra A B₁'] [Algebra B₁' B₁] [Algebra A B₁] [IsScalarTower A B₁' B₁]
      [Algebra A B₂'] [Algebra B₂' B₂] [Algebra A B₂] [IsScalarTower A B₂' B₂]
      [Module.Flat A (B₁ × B₂)] [Module.Flat A B₁] [Module.Flat A B₂]
      (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A B₁)
      (h_quasiFinite₂ : Algebra.FiniteType.QuasiFinite A B₂)
      [Module.Finite A B₁'] [Module.Finite A B₂']
      [h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁)))]
      [h_open₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₂' B₂)))]
      (τ : Algebra.RelativeDualizingModule.of A (B₁' × B₂') (B₁ × B₂)
        (prod h_quasiFinite₁ h_quasiFinite₂) inferInstance)
      (hτ : IsUniversal A (B₁' × B₂') (B₁ × B₂)
        (prod h_quasiFinite₁ h_quasiFinite₂)
        inferInstance τ),
      IsUniversal A B₁' B₁ h_quasiFinite₁ h_open₁
        (prodComparisonOf A B₁' B₁ B₂' B₂ h_quasiFinite₁ h_quasiFinite₂ τ).1)

#check
  (Algebra.RelativeDualizingModule.TraceElement.prodSnd :
    ∀ (A B₁' B₁ B₂' B₂ : Type u)
      [CommRing A] [CommRing B₁'] [CommRing B₁] [CommRing B₂'] [CommRing B₂]
      [IsNoetherianRing A] [IsNoetherianRing B₁] [IsNoetherianRing B₂]
      [Algebra A B₁'] [Algebra B₁' B₁] [Algebra A B₁] [IsScalarTower A B₁' B₁]
      [Algebra A B₂'] [Algebra B₂' B₂] [Algebra A B₂] [IsScalarTower A B₂' B₂]
      [Module.Flat A (B₁ × B₂)] [Module.Flat A B₁] [Module.Flat A B₂]
      (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A B₁)
      (h_quasiFinite₂ : Algebra.FiniteType.QuasiFinite A B₂)
      [Module.Finite A B₁'] [Module.Finite A B₂']
      [h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁)))]
      [h_open₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₂' B₂)))]
      (τ : Algebra.RelativeDualizingModule.of A (B₁' × B₂') (B₁ × B₂)
        (prod h_quasiFinite₁ h_quasiFinite₂) inferInstance)
      (hτ : IsUniversal A (B₁' × B₂') (B₁ × B₂)
        (prod h_quasiFinite₁ h_quasiFinite₂)
        inferInstance τ),
      IsUniversal A B₂' B₂ h_quasiFinite₂ h_open₂
        (prodComparisonOf A B₁' B₁ B₂' B₂ h_quasiFinite₁ h_quasiFinite₂ τ).2)
